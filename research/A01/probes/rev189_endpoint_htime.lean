import NSFormalization.Section4.A01.PressureRegularity

/-!
Reviewer probe for lane 189.  The field below is smooth relative to the
half-open slab, but its ambient two-sided `temporalDerivative` is discontinuous
at the initial endpoint.  This verifies that `htime` is not a consequence of
`hc3` under the tree's `fderiv` convention.
-/

open Set
open NavierStokes.ProblemStatement
open scoped ContDiff

noncomputable section

abbrev rev189e0 : Space := coordinateVector 0

def rev189AbsVelocity : VelocityField := fun z => |z.1| • rev189e0

lemma rev189AbsVelocity_hc3 : ContDiffOn ℝ ∞ rev189AbsVelocity
    (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  have hgood : ContDiffOn ℝ ∞ (fun z : SpaceTime => z.1 • rev189e0)
      (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    contDiffOn_fst.smul contDiffOn_const
  apply hgood.congr
  intro z hz
  simp [rev189AbsVelocity, abs_of_nonneg hz.1.1]

lemma rev189AbsVelocity_temporal_coord (t : ℝ) :
    (temporalDerivative rev189AbsVelocity t 0) 0 = deriv abs t := by
  unfold temporalDerivative rev189AbsVelocity
  rcases eq_or_ne t 0 with rfl | ht
  · have hnot : ¬ DifferentiableAt ℝ (fun s : ℝ => |s| • rev189e0) 0 := by
      intro h
      apply not_differentiableAt_abs_zero
      have hp := (EuclideanSpace.proj (𝕜 := ℝ) 0).differentiableAt.comp 0 h
      simpa [Function.comp_def, rev189e0, coordinateVector, PiLp.single_apply] using hp
    rw [fderiv_zero_of_not_differentiableAt hnot, deriv_abs_zero]
    rfl
  · have hd := (hasDerivAt_abs ht).smul_const rev189e0
    rw [hd.hasFDerivAt.fderiv, deriv_abs]
    simp [rev189e0, coordinateVector]

lemma rev189_deriv_abs_not_continuousOn_Ico :
    ¬ ContinuousWithinAt (fun t : ℝ => deriv abs t) (Ico 0 1) 0 := by
  intro h
  rw [Metric.continuousWithinAt_iff] at h
  obtain ⟨δ, hδ, hb⟩ := h (1 / 2 : ℝ) (by norm_num)
  let x : ℝ := min (δ / 2) (1 / 2)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hxδ : dist x 0 < δ := by
    rw [Real.dist_eq]
    simp only [sub_zero, abs_of_pos hx]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hbad := hb (show x ∈ Ico (0 : ℝ) 1 from ⟨hx.le, hx1⟩) hxδ
  rw [deriv_abs_pos hx, deriv_abs_zero] at hbad
  norm_num at hbad

example : ¬ ContDiffOn ℝ ∞
    (fun z : SpaceTime => temporalDerivative rev189AbsVelocity z.1 z.2)
    (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  intro htime
  have hp : ContinuousOn (fun t : ℝ => ((t, 0) : SpaceTime)) (Ico (0 : ℝ) 1) :=
    continuousOn_id.prodMk continuousOn_const
  have hm : MapsTo (fun t : ℝ => ((t, 0) : SpaceTime)) (Ico (0 : ℝ) 1)
      (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
    intro t ht
    exact ⟨ht, mem_univ _⟩
  have hpath : ContinuousOn
      (fun t : ℝ => temporalDerivative rev189AbsVelocity t 0) (Ico (0 : ℝ) 1) := by
    simpa [Function.comp_def] using htime.continuousOn.comp hp hm
  have hcoord : ContinuousOn
      (fun t : ℝ => (temporalDerivative rev189AbsVelocity t 0) 0) (Ico (0 : ℝ) 1) := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.comp_continuousOn hpath
  have hderiv : ContinuousOn (fun t : ℝ => deriv abs t) (Ico (0 : ℝ) 1) := by
    exact hcoord.congr (fun t _ => (rev189AbsVelocity_temporal_coord t).symm)
  exact rev189_deriv_abs_not_continuousOn_Ico (hderiv 0 (by norm_num))
