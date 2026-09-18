import NSFormalization.Section3.T11.LocalExistenceProbe

noncomputable section
namespace NSFormalization.Section3.T11.Review311

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

-- Negative mutation: the proved contraction constant `1` is tightened to `1 / 2`.
/--
error: Type mismatch
  torusHeat_norm_le s hν ht A
has type
  ‖torusHeat s hν ht A‖ ≤ ‖A‖
but is expected to have type
  ‖torusHeat s hν ht A‖ ≤ 1 / 2 * ‖A‖
-/
#guard_msgs in
example (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (A : PeriodicSobolev s) :
    ‖torusHeat s hν ht A‖ ≤ (1 / 2 : ℝ) * ‖A‖ := by
  exact torusHeat_norm_le s hν ht A

-- The tightened constant is genuinely false: at time zero a nonzero constant
-- mode is fixed by the heat evolution.
example : ¬ ∀ A : PeriodicSobolev 0,
    ‖torusHeat 0 (show (0 : ℝ) ≤ 1 by norm_num) (le_refl 0) A‖ ≤
      (1 / 2 : ℝ) * ‖A‖ := by
  intro h
  let A : PeriodicSobolev 0 := torusConstantDatum 0 (coordinateVector 0)
  have hA : A ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun B : PeriodicSobolev 0 ↦ B.1 0 0) hzero
    simp [A, torusConstantDatum, coordinateVector, lp.single_apply] at hcoeff
  have hpos : 0 < ‖A‖ := (norm_pos_iff.mpr hA)
  have hb := h A
  rw [torusHeat_zero] at hb
  nlinarith

-- Independent non-vacuity check: both the force and solution are nonzero.
example :
    ∃ (K : ℝ≥0∞) (a : SpatialField) (g : SpaceTimeField),
      K ≠ ⊤ ∧ a ∈ initialClassT ∧ periodicSobolevENorm 1 a ≤ K ∧
      ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧
        w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 :=
  nonzero_forced_witness

end NSFormalization.Section3.T11.Review311
