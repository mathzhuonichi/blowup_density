import Formal.R3SolenoidalSobolevCarrier

namespace MNS2

noncomputable section

def r3RawDivergencePointwise (ξ : R3) (v : R3C) : ℂ :=
  ((ξ 0 : ℝ) : ℂ) * v 0 + ((ξ 1 : ℝ) : ℂ) * v 1 + ((ξ 2 : ℝ) : ℂ) * v 2

def r3NormalizedDivergencePointwise (ξ : R3) (v : R3C) : ℂ :=
  r3NormalizedFrequencyCoordinate 0 ξ * v 0 +
  r3NormalizedFrequencyCoordinate 1 ξ * v 1 +
  r3NormalizedFrequencyCoordinate 2 ξ * v 2

theorem r3NormalizedDivergencePointwise_eq_zero_iff
    (ξ : R3) (v : R3C) :
    r3NormalizedDivergencePointwise ξ v = 0 ↔
      r3RawDivergencePointwise ξ v = 0 := by
  have hsR : r3FrequencyL1Scale ξ ≠ 0 := ne_of_gt (r3FrequencyL1Scale_pos ξ)
  have hsC : (((r3FrequencyL1Scale ξ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hsR
  unfold r3NormalizedDivergencePointwise r3NormalizedFrequencyCoordinate
    r3RawDivergencePointwise
  simp only [Complex.ofReal_div]
  field_simp [hsC] <;> simp

end

end MNS2
