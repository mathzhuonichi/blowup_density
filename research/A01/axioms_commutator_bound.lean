import NSFormalization.Section4.A01.CommutatorBound

noncomputable section
namespace NSFormalization.Section4.A01
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerFiniteMetricEnergy
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Actual compatible finite zero elements satisfy the residual inequality,
-- without assuming the globally quantified analytic input.
example (q : ℕ) (hq : 6 ≤ q) (i : Fin 4) :
    restrictOperator 1 (by omega : q+1 ≤ 2+q) (0 : SobolevSpace 1 (2+q)) = 0 ∧
    familyNorm (cylinderCoordinateCommutator hq 0 0 i) ≤
      (4 * A q) * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (0 : SobolevSpace 1 (q+1))‖ * cylinderWordGradient (0 : SobolevSpace 1 (2+q)) := by
  simp [cylinderCoordinateCommutator, familyNorm, familySquaredNorm]

example (q : ℕ) (hq : 6 ≤ q) :
    familyNorm (cylinderCommutator hq 0 0) ≤
      A q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (0 : SobolevSpace 1 (q+1))‖) * cylinderWordGradient (0 : SobolevSpace 1 (2+q)) := by
  simp [cylinderCommutator, familyNorm, familySquaredNorm]

-- A signed pairing estimate cannot bound the norm of an orthogonal residual.
example : (1 : ℝ) * 0 ≤ 0 ∧ ¬ (|1| ≤ (0 : ℝ)) := by norm_num

#print axioms cylinderWordGradient
#print axioms cylinderCoordinateCommutator
#print axioms cylinderCommutator_eq_sum
#print axioms cylinderCoordinateCommutator_empty
#print axioms cylinderCommutator_empty
#print axioms CylinderCoordinateTame
#print axioms cylinderCommutator_le
#print axioms cylinderCommutatorBound_exists
#print axioms cylinderCommutatorBound
#print axioms forcingFamilyBound_of_cylinder'

end NSFormalization.Section4.A01
