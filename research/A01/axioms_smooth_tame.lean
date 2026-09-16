import NSFormalization.Section4.A01.SmoothTame

noncomputable section
namespace NSFormalization.Section4.A01
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerFiniteMetricEnergy
  EulerTransportDerivatives EulerCylinderSobolev
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Actual compatible zero data; no universal tame premise is assumed.
example (q : ℕ) (hq : 6 ≤ q) (C : ℝ) (i : Fin 4) :
    familyNorm (cylinderCoordinateCommutator hq 0 0 i) ≤
      C * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (0 : SobolevSpace 1 (q+1))‖ * cylinderWordGradient (0 : SobolevSpace 1 (2+q)) := by
  simp [cylinderCoordinateCommutator, familyNorm, familySquaredNorm]

example (q : ℕ) (hq : 6 ≤ q) :
    cylinderWordMaximum (0 : SobolevSpace 1 (2+q)) 4 *
        cylinderWordMaximum (0 : SobolevSpace 1 (2+q)) 5 ≤
      ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (restrictOperator 1 (by omega : q+1 ≤ 2+q) (0 : SobolevSpace 1 (2+q)))‖ *
          cylinderWordGradient (0 : SobolevSpace 1 (2+q)) :=
  cylinderWordMaximum_product_le_gradient hq 0 (by omega) (by omega)
    (by omega) (by omega) (by omega)

#print axioms cylinderWordMaximum
#print axioms cylinderWord_norm_le_maximum
#print axioms cylinderWordMaximum_nonneg
#print axioms cylinderWord_square_le_product
#print axioms cylinderWordMaximum_logconvex
#print axioms cylinderWordMaximum_cross
#print axioms cylinderWordMaximum_pair
#print axioms cylinderWordMaximum_between
#print axioms cylinderWordMaximum_le_restrict
#print axioms cylinderWordMaximum_product_le
#print axioms cylinderWordMaximum_le_gradient
#print axioms cylinderWordMaximum_product_le_gradient

#print axioms cylinderMixedProduct_left

end NSFormalization.Section4.A01
