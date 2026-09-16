import Bindings.MainThresholds
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open scoped ENNReal
-- Extract an actual force at a finite positive radius, rather than only a density proposition.
example : ∃ f : SpaceTimeField, MemForceR f ∧
    maximalLifespanR 1 0 f ≤ ENNReal.ofReal 1 ∧
    forceSobolevENorm 2 (-1) (f - 0) < 1 := by
  have hd := mainThresholds.fixedInitialDensity 1 (by norm_num) 1 (by norm_num)
    2 (Or.inr rfl) (-1) 0
    NSFormalization.Section4.A04.zero_mem_initialClassR (by norm_num [criticalOrder])
  obtain ⟨f, hf, hn⟩ := hd 0 NSFormalization.Section4.A04.memForceR_zero 1 (by norm_num)
  exact ⟨f, hf.1, hf.2, hn⟩
-- Positive horizon implies genuinely nonempty history for small positive epsilon.
example {T : ℝ} (hT : 0 < T) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < T - 2 * ε ^ 2 := by
  refine ⟨min 1 (T / 4), lt_min (by norm_num) (by positivity), ?_⟩
  have h0 : 0 ≤ min 1 (T / 4) := le_of_lt (lt_min (by norm_num) (by positivity))
  have h1 := min_le_left (1 : ℝ) (T / 4)
  have h2 := min_le_right (1 : ℝ) (T / 4)
  nlinarith [mul_self_le_mul_self h0 h1]
