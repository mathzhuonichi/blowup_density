import NSFormalization.Paper1.PeriodicTransportDifference

noncomputable section
namespace NSFormalization.Paper1.PeriodicTransportDifference

open PeriodicCrossComponentTransport PeriodicFiniteVectorBound PeriodicLerayCoeffCore PeriodicHeatMultiplier
open scoped BigOperators

/-- A finite weighted contract for the quadratic transport difference. -/
structure FiniteWeightedDifferenceContract (u v : FiniteVector)
    (K : Finset PeriodicFrequency) (A B : ℝ) : Prop where
  hA : 0 ≤ A
  hB : 0 ≤ B
  bound_left : ∀ k, k ∈ K → transportBound (u - v) u k ≤ A
  bound_right : ∀ k, k ∈ K → transportBound v (u - v) k ≤ B

/-- Explicit weighted sum estimate for the genuine cross-component quadratic
transport difference. The weight is any nonnegative scalar function on K. -/
theorem weighted_transport_difference_le_of_contract
    {u v : FiniteVector} {K : Finset PeriodicFrequency} {A B : ℝ}
    (C : FiniteWeightedDifferenceContract u v K A B)
    (w : PeriodicFrequency → ℝ) (hw : ∀ k, k ∈ K → 0 ≤ w k) (ν t : ℝ) :
    (∑ k ∈ K, w k *
      (∑ i : Fin 3, ‖(heatSymbol ν t k : ℂ) *
        (transportCoeffConv u u i k - transportCoeffConv v v i k)‖)) ≤
      ∑ k ∈ K, w k * (heatSymbol ν t k * (A + B)) := by
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (hw k hk)
  apply (heat_transport_difference_norm_le ν t u v k).trans
  apply mul_le_mul_of_nonneg_left _ (heatSymbol_nonneg ν t k)
  exact add_le_add (C.bound_left k hk) (C.bound_right k hk)

end NSFormalization.Paper1.PeriodicTransportDifference
