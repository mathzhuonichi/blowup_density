import Formal.R3L2CoordinateAux
import Formal.R3SolenoidalSobolevCarrier

namespace MNS2

open MeasureTheory Filter

noncomputable section

def r3NormalizedDivergenceTermAux (i : Fin 3) :
    R3L2Velocity →L[ℂ] R3L2ScalarAux :=
  r3L2ScalarMultiplierAux (r3NormalizedFrequencyCoordinateLpTop i) ∘L
    r3L2CoordinateAux i

theorem r3NormalizedDivergenceTermAux_ae (i : Fin 3) (f : R3L2Velocity) :
    r3NormalizedDivergenceTermAux i f =ᵐ[volume]
      fun ξ => r3NormalizedFrequencyCoordinate i ξ * f ξ i := by
  filter_upwards
    [r3L2ScalarMultiplierAux_ae
      (r3NormalizedFrequencyCoordinateLpTop i) (r3L2CoordinateAux i f),
     r3L2CoordinateAux_ae i f,
     r3NormalizedFrequencyCoordinateLpTop_ae i]
    with ξ hmul hcoord hm
  simpa [r3NormalizedDivergenceTermAux, hcoord, hm] using hmul

end

end MNS2
