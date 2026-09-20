import NSFormalization.Section4.A01.ConstructorAssembly

/-! Reviewer counterexample to the pressure-supplier quantifiers in the
committed pipeline probe: an arbitrary smooth velocity need not have L2 raw
pressure-gradient slices. -/

noncomputable section

namespace Rev180H189Unsat

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff

def linearConstantVelocity : SpaceTimeField :=
  fun z => z.1 • coordinateVector 0

lemma linearConstantVelocity_smooth : ContDiff ℝ ∞ linearConstantVelocity := by
  exact contDiff_fst.smul contDiff_const

lemma linearConstantVelocity_pressureGradient (t : ℝ) (x : Space) :
    pressureGradientOfVelocity 1 0 linearConstantVelocity (t, x) =
      -coordinateVector 0 := by
  have ht : deriv (fun s : ℝ => s • coordinateVector 0) t = coordinateVector 0 := by
    simpa using ((hasDerivAt_id t).smul_const (coordinateVector 0)).deriv
  simp [pressureGradientOfVelocity, momentumResidualOfVelocity,
    linearConstantVelocity, temporalDerivative, advection, spatialLaplacian,
    spatialDerivative, ht]

example : ¬ (∀ (velocity : SpaceTimeField),
    ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) →
    ∃ G : SpaceTimeField,
      (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        G (t, x) = pressureGradientOfVelocity 1 0 velocity (t, x)) ∧
      (ContDiffOn ℝ ∞ G (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) ∧
        ∀ t ∈ Ico (0 : ℝ) 1,
          MemLp (fun x : Space => G (t, x)) 2 volume ∧
          RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x)))) := by
  intro h
  obtain ⟨G, hG_int, _hG_smooth, hG⟩ :=
    h linearConstantVelocity linearConstantVelocity_smooth.contDiffOn
  have htIoo : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have htIco : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 := by norm_num
  have hfun : (fun x : Space => G (1 / 2, x)) =
      fun _ : Space => -coordinateVector 0 := by
    funext x
    rw [hG_int (1 / 2) htIoo x]
    exact linearConstantVelocity_pressureGradient (1 / 2) x
  have hmem := (hG (1 / 2) htIco).1
  rw [hfun] at hmem
  rcases (memLp_const_iff (p := 2) two_ne_zero (by simp)).mp hmem with hz | hfinite
  · have hcoord := congrArg (fun v : Space => v 0) hz
    simp [coordinateVector] at hcoord
  · simp at hfinite

end Rev180H189Unsat
