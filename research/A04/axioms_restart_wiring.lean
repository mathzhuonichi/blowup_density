import NSFormalization.Section4.A04.RestartWiring
import NSFormalization.Section4.A04.ZeroSolution

open NSFormalization.Section4
open A02 A04
open scoped ENNReal

#print axioms map_forceTimeMeasure_shift_le
#print axioms restart_force
#print axioms local_restart
#print axioms localCarrier_hasSmoothSobolevPath
#print axioms uniform_local_restart_H7

example : MemForceR (timeShift 1 (0 : SpaceTimeField)) :=
  restart_force 0 memForceR_zero 1 (by norm_num)

example : Nonempty (ClassicalSolutionR 1
    (fun x => (zeroSol 1 1 (by norm_num) (by norm_num)).velocity (0, x))
    (timeShift 0 (0 : SpaceTimeField))
    (A01.localHorizon' 1
      (fun x => (zeroSol 1 1 (by norm_num) (by norm_num)).velocity (0, x))
      (timeShift 0 (0 : SpaceTimeField)))) := by
  exact ⟨(A01.localCarrier 1 _ _ (by norm_num)
    ((zeroSol 1 1 (by norm_num) (by norm_num)).restart_datum ⟨le_rfl, by norm_num⟩)
    (restart_force 0 memForceR_zero 0 le_rfl)).w⟩
