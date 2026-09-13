import Mathlib.Analysis.Fourier.LpSpace
import Formal.R3SolenoidalSobolevCarrier

namespace MNS2

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

def r3NormalizedFrequencyCoordinateLpTop (i : Fin 3) :
    Lp ℂ ⊤ (volume : Measure R3) :=
  (memLp_top_of_bound
      (continuous_r3NormalizedFrequencyCoordinate i).aestronglyMeasurable
      1
      (ae_of_all _ fun ξ => norm_r3NormalizedFrequencyCoordinate_le_one i ξ)).toLp
    (r3NormalizedFrequencyCoordinate i)

theorem r3NormalizedFrequencyCoordinateLpTop_ae (i : Fin 3) :
    r3NormalizedFrequencyCoordinateLpTop i =ᵐ[volume]
      r3NormalizedFrequencyCoordinate i := by
  unfold r3NormalizedFrequencyCoordinateLpTop
  exact MemLp.coeFn_toLp _

end

end MNS2
