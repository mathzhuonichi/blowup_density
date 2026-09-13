import Formal.R3NormalizedDivergenceFrequency

namespace MNS2
noncomputable section

def r3NormalizedDivergenceL2OperatorAux : R3L2Velocity →L[ℂ] R3L2ScalarAux :=
  r3NormalizedDivergenceFrequencyAux ∘L FourierTransform.fourierCLM ℂ R3L2Velocity

def r3L2SolenoidalSubmodule : Submodule ℂ R3L2Velocity :=
  r3NormalizedDivergenceL2OperatorAux.ker

abbrev R3HsSolenoidalVelocity (_s : ℝ) := ↥r3L2SolenoidalSubmodule
abbrev R3HmSolenoidalVelocity (m : ℕ) := R3HsSolenoidalVelocity (m : ℝ)

end
end MNS2
