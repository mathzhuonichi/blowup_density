import NSFormalization.Section3.T11.H1Restart
import TestSupport.Axioms

#print axioms NSFormalization.Section3.T11.periodicGradient_bridgeT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicGradient_bridgeT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicGradient_bridgeT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.hasSum_lTwoSqT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.hasSum_lTwoSqT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.hasSum_lTwoSqT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.periodicHOne_bridgeT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicHOne_bridgeT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicHOne_bridgeT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.periodicHTwo_bridgeT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicHTwo_bridgeT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicHTwo_bridgeT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.periodicL2Energy_eq_lTwoSqT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicL2Energy_eq_lTwoSqT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicL2Energy_eq_lTwoSqT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.periodicGradientEnergy_eq_gradientSqT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicGradientEnergy_eq_gradientSqT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicGradientEnergy_eq_gradientSqT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.periodicHessianEnergy_eq_laplacianSqT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicHessianEnergy_eq_laplacianSqT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicHessianEnergy_eq_laplacianSqT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.enstrophy_differential_on_IccT'
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.enstrophy_differential_on_IccT'
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.enstrophy_differential_on_IccT'
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.continuousOn_periodicSobolevEnergyT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.continuousOn_periodicSobolevEnergyT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.continuousOn_periodicSobolevEnergyT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.differentiableAt_periodicSobolevEnergyT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.differentiableAt_periodicSobolevEnergyT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.differentiableAt_periodicSobolevEnergyT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.timeShiftT_lTwoSq_le_forceL2CapT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.timeShiftT_lTwoSq_le_forceL2CapT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.timeShiftT_lTwoSq_le_forceL2CapT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.inhomogeneousEnergyIdentity_smoothT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.inhomogeneousEnergyIdentity_smoothT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.inhomogeneousEnergyIdentity_smoothT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.weightedEnergyIdentity_smoothT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.weightedEnergyIdentity_smoothT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.weightedEnergyIdentity_smoothT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.enstrophy_differential_smoothT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.enstrophy_differential_smoothT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.enstrophy_differential_smoothT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.periodicHTwo_lintegral_eqT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicHTwo_lintegral_eqT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicHTwo_lintegral_eqT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.uniform_periodicHTwo_running_boundT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.uniform_periodicHTwo_running_boundT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.uniform_periodicHTwo_running_boundT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.uniform_periodicHTwo_endpoint_boundT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.uniform_periodicHTwo_endpoint_boundT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.uniform_periodicHTwo_endpoint_boundT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.periodicHThree_energy_smoothT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicHThree_energy_smoothT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicHThree_energy_smoothT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.periodicHThree_bound_smoothT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.periodicHThree_bound_smoothT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.periodicHThree_bound_smoothT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.shifted_horizon_extensionT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.shifted_horizon_extensionT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.shifted_horizon_extensionT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.exists_maximal_smoothT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.exists_maximal_smoothT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.exists_maximal_smoothT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.uniform_periodicHOne_lifespanT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.uniform_periodicHOne_lifespanT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.uniform_periodicHOne_lifespanT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms NSFormalization.Section3.T11.h1RestartT
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.h1RestartT
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.h1RestartT
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"
