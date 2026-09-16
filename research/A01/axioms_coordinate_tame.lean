import NSFormalization.Section4.A01.CoordinateTame

noncomputable section
namespace NSFormalization.Section4.A01
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerFiniteMetricEnergy
  EulerTransportDerivatives EulerCylinderSobolev
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Compatible zero data, with arbitrary real C: no universal tame premise is assumed.
example (q : ℕ) (hq : 6 ≤ q) (C : ℝ) (i : Fin 4) :
    restrictOperator 1 (by omega : q+1 ≤ 2+q) (0 : SobolevSpace 1 (2+q)) = 0 ∧
    familyNorm (cylinderCoordinateCommutator hq 0 0 i) ≤
      C * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (0 : SobolevSpace 1 (q+1))‖ * cylinderWordGradient (0 : SobolevSpace 1 (2+q)) := by
  simp [cylinderCoordinateCommutator, familyNorm, familySquaredNorm]

example (q : ℕ) (hq : 6 ≤ q) (C : ℝ) :
    familyNorm (cylinderCommutator hq 0 0) ≤
      coordinateTameA q C * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (0 : SobolevSpace 1 (q+1))‖) * cylinderWordGradient (0 : SobolevSpace 1 (2+q)) := by
  simp [cylinderCommutator, familyNorm, familySquaredNorm]

-- Enlarging the candidate is arithmetic; no analytic constant is certified by it.
example (q : ℕ) (C : ℝ) : A q ≤ coordinateTameA q C := le_max_left _ _

#print axioms cylinderLeibniz
#print axioms cylinderLeibniz_eq
#print axioms cylinderCommutatorLeibniz
#print axioms cylinderCommutatorLeibniz_eq
#print axioms cylinderCoordinateLeibniz_sign
#print axioms cylinderWordGradient_continuous
#print axioms cylinderCoordinateCommutator_continuous
#print axioms SmoothCylinderCoordinateTame
#print axioms cylinderCoordinateTame
#print axioms cylinderCoordinateTame_exists
#print axioms smoothCylinderCoordinateTame_iff
#print axioms coordinateTameA
#print axioms coordinateTameA_nonneg
#print axioms coordinateTameA_absorbs
#print axioms cylinderCommutatorBound_recut
#print axioms cylinderCommutatorBound_of_smooth
#print axioms forcingFamilyBound_of_cylinder_recut
#print axioms forcingFamilyBound_of_smooth

end NSFormalization.Section4.A01
