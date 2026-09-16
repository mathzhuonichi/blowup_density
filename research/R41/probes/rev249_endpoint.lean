import Bindings.MainThresholds
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open scoped ENNReal
-- Substantive mutation: make the strict density threshold inclusive.
example : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
      RelativelyDense q s forceClassR (breakdownSetRZero ν T) ↔
        s ≤ criticalOrder q.toReal :=
  mainThresholds.zeroInitialDensityIff
