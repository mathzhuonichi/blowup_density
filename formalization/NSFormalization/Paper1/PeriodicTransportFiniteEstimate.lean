import NSFormalization.Paper1.PeriodicCrossComponentTransportBilinear

/-! Explicit finite-frequency bounds for the actual cross-component transport.

The constant depends on the common support cardinality and a derivative-symbol
bound. These estimates do not assert bounds uniform in the Fourier cutoff.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicCrossComponentTransport

open NSFormalization.Paper1.PeriodicFiniteVectorBound
open NSFormalization.Paper1.PeriodicLerayCoeffCore
open scoped BigOperators

/-- A coefficient bound for the actual transport term with explicit finite
support and derivative constants. The bound on the second input is needed only
at the shifted frequencies sampled by the first input. -/
theorem norm_transportCoeffConv_le_of_support_bound
    (u v : FiniteVector) (S : Finset PeriodicFrequency)
    (i : Fin 3) (k : PeriodicFrequency) (M D N : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hN : 0 ≤ N)
    (huS : ∀ j, (u j).support ⊆ S)
    (hu : ∀ j l, l ∈ S → ‖u j l‖ ≤ M)
    (hd : ∀ j l, l ∈ S → ‖derivativeSymbol j (k - l)‖ ≤ D)
    (hv : ∀ l, l ∈ S → ‖v i (k - l)‖ ≤ N) :
    ‖transportCoeffConv u v i k‖ ≤ 3 * (S.card : ℝ) * M * D * N := by
  classical
  rw [transportCoeffConv_eq_transportCoeff]
  calc
    ‖transportCoeff u v i k‖ ≤
        ∑ j : Fin 3, ∑ l ∈ (u j).support,
          ‖u j l‖ * ‖derivativeSymbol j (k - l)‖ * ‖v i (k - l)‖ :=
      norm_transportCoeff_le u v i k
    _ ≤ ∑ _j : Fin 3, (S.card : ℝ) * (M * D * N) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∑ l ∈ (u j).support,
            ‖u j l‖ * ‖derivativeSymbol j (k - l)‖ * ‖v i (k - l)‖) ≤
            ∑ _l ∈ (u j).support, M * D * N := by
          apply Finset.sum_le_sum
          intro l hl
          have hlS := huS j hl
          exact mul_le_mul
            (mul_le_mul (hu j l hlS) (hd j l hlS) (norm_nonneg _) hM)
            (hv l hlS) (norm_nonneg _) (mul_nonneg hM hD)
        _ = ((u j).support.card : ℝ) * (M * D * N) := by simp
        _ ≤ (S.card : ℝ) * (M * D * N) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (mul_nonneg hM hD) hN)
          exact_mod_cast Finset.card_le_card (huS j)
    _ = 3 * (S.card : ℝ) * M * D * N := by
      simp
      ring

/-- Summing the component estimate gives an explicit bound for the three
output components at a fixed frequency. -/
theorem sum_norm_transportCoeffConv_le_of_support_bound
    (u v : FiniteVector) (S : Finset PeriodicFrequency)
    (k : PeriodicFrequency) (M D N : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hN : 0 ≤ N)
    (huS : ∀ j, (u j).support ⊆ S)
    (hu : ∀ j l, l ∈ S → ‖u j l‖ ≤ M)
    (hd : ∀ j l, l ∈ S → ‖derivativeSymbol j (k - l)‖ ≤ D)
    (hv : ∀ i l, l ∈ S → ‖v i (k - l)‖ ≤ N) :
    (∑ i : Fin 3, ‖transportCoeffConv u v i k‖) ≤
      9 * (S.card : ℝ) * M * D * N := by
  calc
    (∑ i : Fin 3, ‖transportCoeffConv u v i k‖) ≤
        ∑ _i : Fin 3, 3 * (S.card : ℝ) * M * D * N := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_transportCoeffConv_le_of_support_bound
        u v S i k M D N hM hD hN huS hu hd (hv i)
    _ = 9 * (S.card : ℝ) * M * D * N := by
      simp
      ring

/-! A cutoff-enlargement wrapper. All estimates are deliberately re-assumed
on the larger finite set; this theorem makes no uniform-limit claim. -/
theorem norm_transportCoeffConv_le_of_support_bound_mono
    (u v : FiniteVector) (S T : Finset PeriodicFrequency)
    (i : Fin 3) (k : PeriodicFrequency) (M D N : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hN : 0 ≤ N)
    (_hST : S ⊆ T)
    (huT : ∀ j, (u j).support ⊆ T)
    (hu : ∀ j l, l ∈ T → ‖u j l‖ ≤ M)
    (hd : ∀ j l, l ∈ T → ‖derivativeSymbol j (k - l)‖ ≤ D)
    (hv : ∀ l, l ∈ T → ‖v i (k - l)‖ ≤ N) :
    ‖transportCoeffConv u v i k‖ ≤ 3 * (T.card : ℝ) * M * D * N := by
  exact norm_transportCoeffConv_le_of_support_bound u v T i k M D N
    hM hD hN huT hu hd hv

/-! Pointwise wrapper for a sequence of finite cutoffs. No supremum or limit is
inferred: each index carries its own explicit hypotheses and constant. -/
theorem norm_transportCoeffConv_le_of_cutoff_sequence
    (u v : ℕ → FiniteVector) (S : ℕ → Finset PeriodicFrequency)
    (i : Fin 3) (k : PeriodicFrequency) (M D N : ℕ → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hD : ∀ q, 0 ≤ D q) (hN : ∀ q, 0 ≤ N q)
    (huS : ∀ q j, (u q j).support ⊆ S q)
    (hu : ∀ q j l, l ∈ S q → ‖u q j l‖ ≤ M q)
    (hd : ∀ q j l, l ∈ S q → ‖derivativeSymbol j (k - l)‖ ≤ D q)
    (hv : ∀ q l, l ∈ S q → ‖v q i (k - l)‖ ≤ N q) (q : ℕ) :
    ‖transportCoeffConv (u q) (v q) i k‖ ≤
      3 * ((S q).card : ℝ) * M q * D q * N q := by
  exact norm_transportCoeffConv_le_of_support_bound (u q) (v q) (S q) i k
    (M q) (D q) (N q) (hM q) (hD q) (hN q) (huS q) (hu q) (hd q) (hv q)

/-- Pointwise aggregate bound along a finite cutoff sequence. -/
theorem sum_norm_transportCoeffConv_le_of_cutoff_sequence
    (u v : ℕ → FiniteVector) (S : ℕ → Finset PeriodicFrequency)
    (k : PeriodicFrequency) (M D N : ℕ → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hD : ∀ q, 0 ≤ D q) (hN : ∀ q, 0 ≤ N q)
    (huS : ∀ q j, (u q j).support ⊆ S q)
    (hu : ∀ q j l, l ∈ S q → ‖u q j l‖ ≤ M q)
    (hd : ∀ q j l, l ∈ S q → ‖derivativeSymbol j (k - l)‖ ≤ D q)
    (hv : ∀ q i l, l ∈ S q → ‖v q i (k - l)‖ ≤ N q) (q : ℕ) :
    (∑ i : Fin 3, ‖transportCoeffConv (u q) (v q) i k‖) ≤
      9 * ((S q).card : ℝ) * M q * D q * N q := by
  exact sum_norm_transportCoeffConv_le_of_support_bound (u q) (v q) (S q) k
    (M q) (D q) (N q) (hM q) (hD q) (hN q) (huS q) (hu q) (hd q) (hv q)

end NSFormalization.Paper1.PeriodicCrossComponentTransport
