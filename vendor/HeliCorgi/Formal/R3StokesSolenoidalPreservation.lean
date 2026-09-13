import Formal.R3StokesDivergenceCommutation

namespace MNS2

open FourierTransform
open scoped FourierTransform

noncomputable section

theorem r3StokesL2Operator_mem_solenoidal
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f : R3L2Velocity) (hf : f ∈ r3L2SolenoidalSubmodule) :
    r3StokesL2Operator hν ht f ∈ r3L2SolenoidalSubmodule := by
  have hf0 : r3NormalizedDivergenceFrequencyAux (𝓕 f) = 0 := by
    simpa [r3L2SolenoidalSubmodule, r3NormalizedDivergenceL2OperatorAux] using hf
  change r3NormalizedDivergenceFrequencyAux (𝓕 (r3StokesL2Operator hν ht f)) = 0
  rw [fourier_r3StokesL2Operator hν ht f,
    r3NormalizedDivergenceFrequencyAux_stokes hν ht (𝓕 f), hf0]
  simp

end

end MNS2
