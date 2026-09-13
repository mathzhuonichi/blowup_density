import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Formal.R3StokesSolenoidalPreservation

namespace MNS2

noncomputable section

def r3StokesHsSolenoidalOperator
    (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    R3HsSolenoidalVelocity s →L[ℂ] R3HsSolenoidalVelocity s :=
  (r3StokesL2Operator hν ht).restrict
    (p := r3L2SolenoidalSubmodule) (q := r3L2SolenoidalSubmodule)
    (fun f hf => r3StokesL2Operator_mem_solenoidal hν ht f hf)

@[simp]
theorem r3StokesHsSolenoidalOperator_coe
    (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f : R3HsSolenoidalVelocity s) :
    ((r3StokesHsSolenoidalOperator s hν ht f : R3HsSolenoidalVelocity s) : R3L2Velocity) =
      r3StokesL2Operator hν ht f.1 := by
  rfl

end

end MNS2
