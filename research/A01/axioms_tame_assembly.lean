import NSFormalization.Section4.A01.TameAssembly

noncomputable section
namespace NSFormalization.Section4.A01
#print axioms cylinderRightProduct_memLp
#print axioms cylinderRightProduct
#print axioms cylinderRightProduct_ae
#print axioms cylinderRightProduct_norm
#print axioms cylinderMixedProduct_right
#print axioms cylinderWord_ae
#print axioms cylinderMixedWord_bound
#print axioms cylinderL2Bound_add
#print axioms cylinderLeibniz_bound
#print axioms cylinderCommutatorLeibniz_bound
#print axioms cylinderDerivative_ae
#print axioms cylinderCoordinateCommutator_ae
#print axioms cylinderCoordinateWord_bound
#print axioms tameAssemblyConstant
#print axioms smoothCylinderCoordinateTame
#print axioms cylinderCoordinateTame_unconditional
#print axioms cylinderCoordinateTame_exists'
#print axioms tameAssemblyA
#print axioms cylinderCommutatorBound_unconditional
#print axioms forcingFamilyBound_unconditional
#print axioms finiteMildEnergy'
#print axioms hb_of_base''
#print axioms strong_time_square_integral_limit
#print axioms mapped_time_square_integral_limit
#print axioms maximal_word_square_integral_limit
#print axioms signed_quotient_absorption
#print axioms CylinderSignedEnergyPassage
#print axioms cylinderSignedRootLimit_of_forcingBound
#print axioms finiteMildEnergy_of_forcingBound'
#print axioms signedWordPath
#print axioms signedApproximationRoot
#print axioms signedApproximationDissipation
#print axioms signedApproximationForcing
#print axioms signedApproximationRoot_apply
#print axioms signedApproximationRoot_tendsto
#print axioms signed_transport_zero
#print axioms signed_source_pairing_le
#print axioms signed_scalar_integral
#print axioms regularized_signed_energy_inequality
#print axioms signed_subintervalWeight_tendsto
#print axioms signed_forcing_integral_tendsto
#print axioms signedRootCoefficient
#print axioms signedRootCoefficient_tendsto
#print axioms signedApproximationForcing_tendsto
#print axioms signed_scalar_multiplier_tendsto
#print axioms signed_weighted_square_limit
#print axioms signedGradientOperator
#print axioms signedGradientOperator_apply
#print axioms signedGradientOperator_norm_sq
#print axioms signedApproximationDissipation_eq
#print axioms signedGradientOperator_ae
#print axioms signedInverseRoot
#print axioms maximal_weighted_dissipation_limit
#print axioms cylinderSignedEnergyPassage
#print axioms cylinderSignedRootLimit_of_forcingBound'
#print axioms finiteMildEnergy_of_forcingBound''

open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerFiniteMetricEnergy
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Actual zero data, without assuming any universal tame premise.
example (q : ℕ) (hq : 6 ≤ q) (i : Fin 4) :
    familyNorm (cylinderCoordinateCommutator hq 0 0 i) ≤
      tameAssemblyConstant q * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (0 : SobolevSpace 1 (q+1))‖ * cylinderWordGradient (0 : SobolevSpace 1 (2+q)) := by
  exact cylinderCoordinateTame_unconditional hq 0 0 (by simp) i

example (q : ℕ) (hq : 6 ≤ q) : ∃ C : ℝ, CylinderCoordinateTame q hq C :=
  cylinderCoordinateTame_exists' hq

end NSFormalization.Section4.A01
