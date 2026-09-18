import NSFormalization.Section3.T15.Scaling
open Set
open NSFormalization.Section3.T15
-- Negative mutation: the placement threshold is changed from the required
-- `2 * ε ^ 2 < T` to `3 * ε ^ 2 < T`; the original conformance proof no longer applies.
example (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, 3 * ε ^ 2 < place.T := by
  exact place.eps_time
