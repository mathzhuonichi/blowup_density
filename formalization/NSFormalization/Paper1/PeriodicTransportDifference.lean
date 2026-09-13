import NSFormalization.Paper1.PeriodicCrossComponentTransportBilinear

/-!
# Quadratic differences of the actual cross-component transport coefficients

This uses the two established additive identities for `(u · ∇)v`. The finite
supports may change under subtraction. No common support, pressure, or PDE
existence hypothesis is needed for the algebraic identity.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicTransportDifference

open PeriodicCrossComponentTransport PeriodicFiniteVectorBound
open PeriodicLerayCoeffCore PeriodicHeatMultiplier
open scoped BigOperators

theorem transport_self_sub_self (u v : FiniteVector) (i : Fin 3)
    (k : PeriodicFrequency) :
    transportCoeffConv u u i k - transportCoeffConv v v i k =
      transportCoeffConv (u - v) u i k + transportCoeffConv v (u - v) i k := by
  have hleft := transportCoeffConv_add_left (u - v) v u i k
  have hright := transportCoeffConv_add_right v (u - v) v i k
  simp only [sub_add_cancel] at hleft hright
  rw [hleft, hright]
  abel

/-- The explicit finite sum controlling a transport coefficient, summed over
the three output components. Its derivative acts on the second input. -/
def transportBound (u v : FiniteVector) (k : PeriodicFrequency) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ l ∈ (u j).support,
    ‖u j l‖ * ‖derivativeSymbol j (k - l)‖ * ‖v i (k - l)‖

theorem transport_difference_norm_le (u v : FiniteVector) (k : PeriodicFrequency) :
    ∑ i : Fin 3, ‖transportCoeffConv u u i k - transportCoeffConv v v i k‖ ≤
      transportBound (u - v) u k + transportBound v (u - v) k := by
  calc
    _ ≤ ∑ i : Fin 3, (‖transportCoeffConv (u - v) u i k‖ +
        ‖transportCoeffConv v (u - v) i k‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [transport_self_sub_self]
      exact norm_add_le _ _
    _ = (∑ i : Fin 3, ‖transportCoeffConv (u - v) u i k‖) +
        ∑ i : Fin 3, ‖transportCoeffConv v (u - v) i k‖ :=
      Finset.sum_add_distrib
    _ ≤ _ := add_le_add (transportCoeffConv_norm_aggregate_le (u - v) u k)
      (transportCoeffConv_norm_aggregate_le v (u - v) k)

/-- Exact heat weighting of the genuine cross-component quadratic difference.
This statement uses positivity of the heat symbol, not a cutoff-dependent
contraction estimate or a physical-space realization. -/
theorem heat_transport_difference_norm_le (ν t : ℝ) (u v : FiniteVector)
    (k : PeriodicFrequency) :
    ∑ i : Fin 3, ‖(heatSymbol ν t k : ℂ) *
      (transportCoeffConv u u i k - transportCoeffConv v v i k)‖ ≤
      heatSymbol ν t k * (transportBound (u - v) u k + transportBound v (u - v) k) := by
  simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (heatSymbol_nonneg ν t k)]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (transport_difference_norm_le u v k)
    (heatSymbol_nonneg ν t k)

end NSFormalization.Paper1.PeriodicTransportDifference
