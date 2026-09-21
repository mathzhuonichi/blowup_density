import NSFormalization.Section4.A01.ConstructorAssembly
import NavierStokes.ResidualRegularity

/-!
Satisfiability and endpoint probes for the supplier-provided pressure-gradient
representative.

The first example takes `G := pressureGradientOfVelocity` when the velocity and
force are smooth on an open neighbourhood of the initial slab.  Its interior
identity is reflexive, and its slab package is obtained by restriction of the
standard open-neighbourhood smoothness and slice properties.

The second example records why the former interface was invalid: for
`u(t,x) = |t| e₀`, the ambient two-sided `fderiv` makes the raw
`pressureGradientOfVelocity` discontinuous at `t = 0`, although `u` is smooth
relative to the half-open slab.
-/

noncomputable section

namespace Rev180PressureGradientRepresentative

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff

/-- On an open neighbourhood, the raw field itself is a valid choice of `G`.
The `MemLp` and symmetric-Jacobian clauses are the standard per-slice
properties that the pressure supplier proves from projected momentum. -/
example {ν S : ℝ} (f velocity : SpaceTimeField)
    (hf : ContDiffOn ℝ ∞ f
      (Ioo (-1 : ℝ) S ×ˢ (univ : Set Space)))
    (hvelocity : ContDiffOn ℝ ∞ velocity
      (Ioo (-1 : ℝ) S ×ˢ (univ : Set Space)))
    (hmem : ∀ t ∈ Ico (0 : ℝ) S,
      MemLp (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))
        2 volume)
    (hsymm : ∀ t ∈ Ico (0 : ℝ) S,
      RadialPotential.HasSymmetricJacobian
        (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))) :
    ∃ G : SpaceTimeField,
      (∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
        G (t, x) = pressureGradientOfVelocity ν f velocity (t, x)) ∧
      (ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
        ∀ t ∈ Ico (0 : ℝ) S,
          MemLp (fun x : Space => G (t, x)) 2 volume ∧
          RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x))) := by
  let Ω : Set SpaceTime := Ioo (-1 : ℝ) S ×ˢ (univ : Set Space)
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_univ
  have hadv := NavierStokes.ResidualRegularity.contDiffOn_advection hΩ hvelocity
  have hlap := NavierStokes.ResidualRegularity.contDiffOn_spatialLaplacian hΩ hvelocity
  have htime := NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative hΩ hvelocity
  have hgradient : ContDiffOn ℝ ∞ (pressureGradientOfVelocity ν f velocity) Ω := by
    change ContDiffOn ℝ ∞ (fun z =>
      f z - advection velocity z.1 z.2 + ν • spatialLaplacian velocity z.1 z.2 -
        temporalDerivative velocity z.1 z.2) Ω
    exact ((hf.sub hadv).add ((contDiffOn_const (c := ν)).smul hlap)).sub htime
  refine ⟨pressureGradientOfVelocity ν f velocity, ?_, ?_, ?_⟩
  · intro t ht x
    rfl
  · apply hgradient.mono
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩
  · intro t ht
    exact ⟨hmem t ht, hsymm t ht⟩

abbrev rev180e₀ : Space := coordinateVector 0

def rev180AbsVelocity : VelocityField := fun z => |z.1| • rev180e₀

lemma rev180AbsVelocity_hc3 : ContDiffOn ℝ ∞ rev180AbsVelocity
    (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  have hgood : ContDiffOn ℝ ∞ (fun z : SpaceTime => z.1 • rev180e₀)
      (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    contDiffOn_fst.smul contDiffOn_const
  apply hgood.congr
  intro z hz
  simp [rev180AbsVelocity, abs_of_nonneg hz.1.1]

lemma rev180AbsVelocity_temporal_coord (t : ℝ) :
    (temporalDerivative rev180AbsVelocity t 0) 0 = deriv abs t := by
  unfold temporalDerivative rev180AbsVelocity
  rcases eq_or_ne t 0 with rfl | ht
  · have hnot : ¬ DifferentiableAt ℝ (fun s : ℝ => |s| • rev180e₀) 0 := by
      intro h
      apply not_differentiableAt_abs_zero
      have hp := (EuclideanSpace.proj (𝕜 := ℝ) 0).differentiableAt.comp 0 h
      simpa [Function.comp_def, rev180e₀, coordinateVector, PiLp.single_apply] using hp
    rw [fderiv_zero_of_not_differentiableAt hnot, deriv_abs_zero]
    rfl
  · have hd := (hasDerivAt_abs ht).smul_const rev180e₀
    rw [hd.hasFDerivAt.fderiv, deriv_abs]
    simp [rev180e₀, coordinateVector]

lemma rev180_deriv_abs_not_continuousOn_Ico :
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

lemma rev180AbsVelocity_pressureGradient_coord (t : ℝ) :
    (pressureGradientOfVelocity 0 0 rev180AbsVelocity (t, 0)) 0 =
      -deriv abs t := by
  change (momentumResidualOfVelocity 0 0 rev180AbsVelocity (t, 0) -
    temporalDerivative rev180AbsVelocity t 0) 0 = -deriv abs t
  rw [show momentumResidualOfVelocity 0 0 rev180AbsVelocity (t, 0) = 0 by
    simp [momentumResidualOfVelocity, rev180AbsVelocity, advection,
      spatialLaplacian, spatialDerivative]]
  simp only [zero_sub, PiLp.neg_apply]
  rw [rev180AbsVelocity_temporal_coord]

/-- The old endpoint premise is false even though the velocity has the exact
relative slab smoothness used by `ClassicalSolutionR`. -/
example : ¬ ContDiffOn ℝ ∞
    (pressureGradientOfVelocity 0 0 rev180AbsVelocity)
    (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  intro hpg
  have hp : ContinuousOn (fun t : ℝ => ((t, 0) : SpaceTime)) (Ico (0 : ℝ) 1) :=
    continuousOn_id.prodMk continuousOn_const
  have hm : MapsTo (fun t : ℝ => ((t, 0) : SpaceTime)) (Ico (0 : ℝ) 1)
      (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
    intro t ht
    exact ⟨ht, mem_univ _⟩
  have hpath : ContinuousOn
      (fun t : ℝ => pressureGradientOfVelocity 0 0 rev180AbsVelocity (t, 0))
      (Ico (0 : ℝ) 1) := by
    simpa [Function.comp_def] using hpg.continuousOn.comp hp hm
  have hcoord : ContinuousOn
      (fun t : ℝ => (pressureGradientOfVelocity 0 0 rev180AbsVelocity (t, 0)) 0)
      (Ico (0 : ℝ) 1) := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.comp_continuousOn hpath
  have hneg : ContinuousOn (fun t : ℝ => -deriv abs t) (Ico (0 : ℝ) 1) := by
    exact hcoord.congr (fun t _ => (rev180AbsVelocity_pressureGradient_coord t).symm)
  have hderiv : ContinuousOn (fun t : ℝ => deriv abs t) (Ico (0 : ℝ) 1) := by
    refine hneg.neg.congr ?_
    intro t ht
    simp
  exact rev180_deriv_abs_not_continuousOn_Ico (hderiv 0 (by norm_num))

end Rev180PressureGradientRepresentative
