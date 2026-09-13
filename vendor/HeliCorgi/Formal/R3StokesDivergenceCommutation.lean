import Formal.R3SolenoidalCarrierCompleteness
import Formal.R3StokesL2Operator

namespace MNS2
open MeasureTheory Filter
noncomputable section

theorem r3NormalizedDivergenceFrequencyAux_stokes
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (f : R3L2Velocity) :
    r3NormalizedDivergenceFrequencyAux (r3StokesL2FrequencyMultiplier hν ht f) =
      r3L2ScalarMultiplierAux (r3StokesScalarLpTop hν ht)
        (r3NormalizedDivergenceFrequencyAux f) := by
  apply Lp.ext
  filter_upwards
    [r3NormalizedDivergenceFrequencyAux_ae (r3StokesL2FrequencyMultiplier hν ht f),
     r3StokesL2FrequencyMultiplier_ae hν ht f,
     r3L2ScalarMultiplierAux_ae (r3StokesScalarLpTop hν ht)
       (r3NormalizedDivergenceFrequencyAux f),
     r3NormalizedDivergenceFrequencyAux_ae f,
     r3StokesScalarLpTop_ae hν ht]
    with ξ h1 h2 h3 h4 h5
  rw [h1, h3, h2, h4, h5]
  simp only [r3NormalizedDivergencePointwise, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

end
end MNS2
