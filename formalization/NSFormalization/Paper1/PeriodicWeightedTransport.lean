import NSFormalization.Paper1.PeriodicTransportFiniteEstimate

noncomputable section
namespace NSFormalization.Paper1.PeriodicCrossComponentTransport

open NSFormalization.Paper1.PeriodicFiniteVectorBound
open NSFormalization.Paper1.PeriodicLerayCoeffCore
open scoped BigOperators

/-- Explicit finite-support contract for a weighted transport estimate.  The
bounds are hypotheses and the resulting constant depends on the cutoff. -/
structure FiniteWeightedTransportContract (u v : FiniteVector)
    (S : Finset PeriodicFrequency) (k : PeriodicFrequency) (M D N : ℝ) : Prop where
  hM : 0 ≤ M
  hD : 0 ≤ D
  hN : 0 ≤ N
  support_u : ∀ j, (u j).support ⊆ S
  coeff_u : ∀ j l, l ∈ S → ‖u j l‖ ≤ M
  derivative : ∀ j l, l ∈ S → ‖derivativeSymbol j (k - l)‖ ≤ D
  coeff_v : ∀ i l, l ∈ S → ‖v i (k - l)‖ ≤ N

/-- Consume the explicit finite-support contract to obtain the audited
aggregate bound. -/
theorem sum_norm_transportCoeffConv_le_of_contract
    {u v : FiniteVector} {S : Finset PeriodicFrequency} {k : PeriodicFrequency}
    {M D N : ℝ} (C : FiniteWeightedTransportContract u v S k M D N) :
    (∑ i : Fin 3, ‖transportCoeffConv u v i k‖) ≤
      9 * (S.card : ℝ) * M * D * N := by
  exact sum_norm_transportCoeffConv_le_of_support_bound u v S k M D N
    C.hM C.hD C.hN C.support_u C.coeff_u C.derivative C.coeff_v

end NSFormalization.Paper1.PeriodicCrossComponentTransport
