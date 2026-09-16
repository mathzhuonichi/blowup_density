import NSFormalization.Section4.R43.CriticalMomentum
import NSFormalization.Section4.A04.ZeroSolution

/-! Lane 219: every explicit declaration, followed by a zero-solution instance. -/

#print axioms NSFormalization.Section4.R43.CarrierWindow.RestartFixedForce
#print axioms NSFormalization.Section4.R43.CarrierWindow.referenceForce_timeShift_norm_le
#print axioms NSFormalization.Section4.R43.CarrierWindow.restartFixedForce_of_memForceR
#print axioms NSFormalization.Section4.R43.CarrierWindow.shiftedSolution
#print axioms NSFormalization.Section4.R43.CarrierWindow.compact_hSeven_bound
#print axioms NSFormalization.Section4.R43.CarrierWindow.exists_carrier_window
#print axioms NSFormalization.Section4.R43.CarrierWindow.classical_hasSmoothSobolevPath
#print axioms NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevScalarLM
#print axioms NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevScalarL
#print axioms NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevVectorL
#print axioms NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevVectorL_apply
#print axioms NSFormalization.Section4.R43.CriticalHomogeneous.chosenHomogeneousDatum_eq
#print axioms NSFormalization.Section4.R43.CriticalHomogeneous.orderTwoToHalf
#print axioms NSFormalization.Section4.R43.CriticalHomogeneous.chosenHomogeneousDatum_eq_orderTwoToHalf
#print axioms NSFormalization.Section4.R43.criticalVelocityHalf_smooth
#print axioms NSFormalization.Section4.R43.criticalVelocityHalf_momentum
#print axioms NSFormalization.Section4.R43.criticalDatumInputs_of_classical
#print axioms NSFormalization.Section4.R43.exists_criticalDatumPath'
#print axioms NSFormalization.Section4.R43.rcritical1_of_classical'

namespace NSFormalization.Section4.R43

/-- The unconditional theorem applies to the genuine zero solution and force. -/
theorem zeroCriticalMomentum :
    CriticalDatumInputs (A04.zeroSol 1 2 (by norm_num) (by norm_num))
      A04.memForceR_zero :=
  criticalDatumInputs_of_classical (by norm_num) A04.memForceR_zero _

#print axioms zeroCriticalMomentum

example : Nonempty
    (CriticalDatumPath (A04.zeroSol 1 2 (by norm_num) (by norm_num))
      A04.memForceR_zero) :=
  exists_criticalDatumPath' (by norm_num) A04.memForceR_zero _

end NSFormalization.Section4.R43
