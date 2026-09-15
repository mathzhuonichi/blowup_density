import NSFormalization.Section4.A01.ConstructorPieces

/-!
Conformance for lane 158 (`Section4/A01/ConstructorPieces.lean`).

* `#print axioms` for the module's declaration = `[propext, Classical.choice, Quot.sound]`.
* Non-vacuity: the supply lemma fires on `u := 0`, `U := 0`, `velocity := 0` (at `q = 6`, `m = 7`,
  `S = 1`), producing a genuine order-7 datum of the (a.e.-`0`) velocity slice — so the lemma is not
  vacuous.
-/

noncomputable section

namespace Axioms158

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerLpTranslation

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

#print axioms hasWeakDerivsL2_of_word_full
#print axioms hasWeakDerivsL2_of_cylinder_full
#print axioms exists_continuous_word_descent
#print axioms exists_isSobolevDatum_slice_of_cylinder

/-- Non-vacuity: fire on `u := 0`, `U := 0`, `velocity := 0`. -/
theorem nonvacuous_datum_slice :
    ∃ A : RealVectorSobolev ((7 : ℕ) : ℝ),
      NSFormalization.Section4.A02.IsSobolevDatum ((7 : ℕ) : ℝ)
        (fun x : Space =>
          (0 : SpaceTimeField) ((⟨0, by norm_num, by norm_num⟩ : Icc (0 : ℝ) 1).1, x)) A :=
  exists_isSobolevDatum_slice_of_cylinder (q := 6) (S := 1)
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7))
    (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
    (by intro θ t; simp)
    (by intro t; simp [value])
    (0 : SpaceTimeField)
    (by
      intro t
      simp only [ContinuousMap.zero_apply]
      filter_upwards [Lp.coeFn_zero (E := Space) (p := 2) (μ := volume)] with x hx
      rw [hx]; rfl)
    (m := 7) (by norm_num) ⟨0, by norm_num, by norm_num⟩

#print axioms nonvacuous_datum_slice

/-- Consume the top-order continuous path and identify its unique zero lift. -/
theorem nonvacuous_word_path :
    ∃ Z : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2), ∀ t, Z t = 0 := by
  obtain ⟨Z, hZ⟩ := exists_continuous_word_descent (q := 6) (S := 1)
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7))
    (by intro θ t; simp) 7 (by norm_num) (fun _ => 0)
  refine ⟨Z, fun t => ordinaryLift.injective ?_⟩
  simpa [word] using hZ t

#print axioms nonvacuous_word_path

end Axioms158
