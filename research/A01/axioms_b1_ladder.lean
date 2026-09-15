import NSFormalization.Section4.A01.DatumPathContinuous

noncomputable section
open Set MeasureTheory
open NSFormalization.Section4.A01 NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

#print axioms continuous_cylinder_word
#print axioms weakDerivsBound_word_top
#print axioms weakDerivsBound_cylinder_top
#print axioms datum_sub_norm_sq_le
#print axioms exists_continuous_datumPath

-- A nonempty interval and the top order, with both cylinder and ordinary paths zero.
example (q : ℕ) :
    ∃ A : Icc (0 : ℝ) 1 → RealVectorSobolev ((q + 1 : ℕ) : ℝ),
      (∀ t, IsSobolevDatum ((q + 1 : ℕ) : ℝ)
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (A t)) ∧ Continuous A := by
  exact exists_continuous_datumPath
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 (q + 1)))
    (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
    (fun θ t => by simp) (fun t => by simp [value]) (q + 1) le_rfl
