import Formal.R3L2ScalarAux
import Formal.R3NormalizedFrequencyLpTop
import Formal.R3CoordinateLinearAux

namespace MNS2

open MeasureTheory

noncomputable section

def r3L2CoordinateAux (i : Fin 3) :
    R3L2Velocity →L[ℂ] R3L2ScalarAux :=
  (r3CoordinateFiberAux i).compLpL 2 (volume : Measure R3)

theorem r3L2CoordinateAux_ae (i : Fin 3) (f : R3L2Velocity) :
    r3L2CoordinateAux i f =ᵐ[volume] fun ξ => f ξ i := by
  exact (r3CoordinateFiberAux i).coeFn_compLpL f

end

end MNS2
