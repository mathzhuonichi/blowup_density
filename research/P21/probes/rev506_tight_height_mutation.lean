import NSFormalization.Section4.A04.EnstrophyBarrier

open Set MeasureTheory
open NSFormalization.Section4.A04

/-!
Reviewer negative probe: the genuine barrier height `2 * (1 + K) - 1` is
tightened to the initial height `K`.  This is false already for `K = F = 0`
and the increasing cubic solution in `b3_closes.lean`.
-/

example {c C K F : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hK : 0 ≤ K) (hF : 0 ≤ F) :
    ∃ d > 0, ∃ M : ℝ, M = K ∧
      ∀ (a S : ℝ) (Y Z : ℝ → ℝ), S ≤ d →
      ContinuousOn Y (Icc a (a + S)) →
      (∀ t ∈ Ioo a (a + S), DifferentiableAt ℝ Y t) →
      (∀ t ∈ Icc a (a + S), 0 ≤ Y t) → Y a ≤ K →
      (∀ t ∈ Ioo a (a + S), 0 ≤ Z t) →
      (∀ t ∈ Ioo a (a + S),
        deriv Y t + c * Z t ≤ C * (1 + Y t) ^ 3 + C * F) →
      ∀ t ∈ Icc a (a + S), Y t ≤ M := by
  exact enstrophy_uniform_barrier hc hC hK hF
