import Formal.R3SolenoidalCarrierCompleteness
import Formal.R3SobolevCarrier

namespace MNS2

open MeasureTheory
open scoped SchwartzMap

noncomputable section

/-- Decode a solenoidal Bessel coordinate through the existing `H^s` tempered-distribution map. -/
def r3HsSolenoidalToTempered (s : ℝ) (u : R3HsSolenoidalVelocity s) :
    𝓢'(R3, R3C) :=
  r3HsToTemperedCLM s u.1

/-- Every solenoidal Bessel coordinate represents an `H^s(R³; C³)` distribution. -/
theorem r3HsSolenoidalToTempered_memSobolev (s : ℝ) (u : R3HsSolenoidalVelocity s) :
    TemperedDistribution.MemSobolev s 2 (r3HsSolenoidalToTempered s u) := by
  exact r3HsToTempered_memSobolev s u.1

/-- Integer-order wrapper for the strong `H^m_σ` carrier. -/
theorem r3HmSolenoidalToTempered_memSobolev (m : ℕ) (u : R3HmSolenoidalVelocity m) :
    TemperedDistribution.MemSobolev (m : ℝ) 2
      (r3HsSolenoidalToTempered (m : ℝ) u) := by
  exact r3HsSolenoidalToTempered_memSobolev (m : ℝ) u

end

end MNS2
