import Formal.R3ClosedSolenoidalCarrier

namespace MNS2
noncomputable section

theorem r3HsSolenoidalVelocity_complete (s : ℝ) :
    CompleteSpace (R3HsSolenoidalVelocity s) := by
  change CompleteSpace r3NormalizedDivergenceL2OperatorAux.ker
  infer_instance

@[simp]
theorem mem_r3L2SolenoidalSubmodule_iff (f : R3L2Velocity) :
    f ∈ r3L2SolenoidalSubmodule ↔ r3NormalizedDivergenceL2OperatorAux f = 0 := by
  simp [r3L2SolenoidalSubmodule]

end
end MNS2
