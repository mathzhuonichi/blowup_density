import NSFormalization.Paper1.PeriodicCriticalBridge

/-!
# Finite low/high frequency splitting for the periodic critical interface

For a finite Fourier packet and a threshold `Λ`, this file separates modes with
`periodicFrequencyWeight ≤ Λ` from the complementary high modes.  The split is
purely finite and exact: both the Fourier sum and every nonnegative spectral
energy decompose as the sum of their low and high pieces.  No estimate uniform
in `Λ` is asserted; the point is to expose the two terms that a future
critical argument must control separately.
-/
noncomputable section
namespace NSFormalization.Paper1

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal

/-- The low-frequency part of a finite spectrum at threshold `Λ`. -/
def lowFrequencySet (S : Finset PeriodicFrequency) (Λ : ℝ) : Finset PeriodicFrequency :=
  S.filter (fun k => periodicFrequencyWeight k ≤ Λ)

/-- The high-frequency part of a finite spectrum at threshold `Λ`. -/
def highFrequencySet (S : Finset PeriodicFrequency) (Λ : ℝ) : Finset PeriodicFrequency :=
  S.filter (fun k => Λ < periodicFrequencyWeight k)

lemma lowFrequencySet_disjoint_highFrequencySet
    (S : Finset PeriodicFrequency) (Λ : ℝ) :
    Disjoint (lowFrequencySet S Λ) (highFrequencySet S Λ) := by
  rw [Finset.disjoint_left]
  intro k hkL hkH
  have hL : periodicFrequencyWeight k ≤ Λ := (Finset.mem_filter.mp hkL).2
  have hH : Λ < periodicFrequencyWeight k := (Finset.mem_filter.mp hkH).2
  exact (not_lt_of_ge hL) hH

lemma lowFrequencySet_union_highFrequencySet
    (S : Finset PeriodicFrequency) (Λ : ℝ) :
    lowFrequencySet S Λ ∪ highFrequencySet S Λ = S := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_union.mp hk with hkL | hkH
    · exact (Finset.mem_filter.mp hkL).1
    · exact (Finset.mem_filter.mp hkH).1
  · intro hkS
    rcases le_or_gt (periodicFrequencyWeight k) Λ with hkL | hkH
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hkS, hkL⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hkS, hkH⟩))

lemma lowFrequencySet_subset (S : Finset PeriodicFrequency) (Λ : ℝ) :
    lowFrequencySet S Λ ⊆ S := by
  intro k hk
  exact (Finset.mem_filter.mp hk).1

lemma highFrequencySet_subset (S : Finset PeriodicFrequency) (Λ : ℝ) :
    highFrequencySet S Λ ⊆ S := by
  intro k hk
  exact (Finset.mem_filter.mp hk).1

/-- Exact decomposition of a finite Fourier sum into low and high modes. -/
theorem finitePeriodicFourierSum_eq_low_add_high
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency) (Λ : ℝ) (x : Space) :
    finitePeriodicFourierSum c S x =
      finitePeriodicFourierSum c (lowFrequencySet S Λ) x +
        finitePeriodicFourierSum c (highFrequencySet S Λ) x := by
  unfold finitePeriodicFourierSum
  rw [← Finset.sum_union (lowFrequencySet_disjoint_highFrequencySet S Λ)]
  rw [lowFrequencySet_union_highFrequencySet]

/-- Any nonnegative finite spectral energy splits exactly at the threshold. -/
lemma sum_split_low_high
    (a : PeriodicFrequency → ℝ)
    (S : Finset PeriodicFrequency) (Λ : ℝ) :
    (∑ k ∈ S, a k) =
      (∑ k ∈ lowFrequencySet S Λ, a k) +
        (∑ k ∈ highFrequencySet S Λ, a k) := by
  rw [← Finset.sum_union (lowFrequencySet_disjoint_highFrequencySet S Λ)]
  rw [lowFrequencySet_union_highFrequencySet]

/-- Exact low/high decomposition of homogeneous half-order energy. -/
theorem homogeneousHalfEnergy_eq_low_add_high
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency) (Λ : ℝ) :
    homogeneousHalfEnergy c S =
      homogeneousHalfEnergy c (lowFrequencySet S Λ) +
        homogeneousHalfEnergy c (highFrequencySet S Λ) := by
  unfold homogeneousHalfEnergy
  rw [← Finset.sum_union (lowFrequencySet_disjoint_highFrequencySet S Λ)]
  rw [lowFrequencySet_union_highFrequencySet]

/-- Exact decomposition of any finite weighted coefficient energy. -/
theorem weightedFiniteEnergy_eq_low_add_high
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency)
    (w : PeriodicFrequency → ℝ) (Λ : ℝ) :
    (∑ k ∈ S, w k * ‖c k‖ ^ 2) =
      (∑ k ∈ lowFrequencySet S Λ, w k * ‖c k‖ ^ 2) +
        (∑ k ∈ highFrequencySet S Λ, w k * ‖c k‖ ^ 2) := by
  rw [← Finset.sum_union (lowFrequencySet_disjoint_highFrequencySet S Λ)]
  rw [lowFrequencySet_union_highFrequencySet]

/- The high-frequency reciprocal multiplier has the elementary finite bound
`card(high) * Λ^(-1/2)`.  This is useful for a two-parameter truncation, but
the cardinality factor is intentionally retained. -/
theorem highFrequency_reciprocalHalfWeight_le_card_mul
    (S : Finset PeriodicFrequency) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    (∑ k ∈ highFrequencySet S Λ,
      (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) ≤
      (highFrequencySet S Λ).card * (Λ ^ (1 / 2 : ℝ))⁻¹ := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hterm : ∀ k ∈ highFrequencySet S Λ,
      (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹ ≤
        (Λ ^ (1 / 2 : ℝ))⁻¹ := by
    intro k hk
    have hkH : Λ < periodicFrequencyWeight k := (Finset.mem_filter.mp hk).2
    have hpow : Λ ^ (1 / 2 : ℝ) ≤
        periodicFrequencyWeight k ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hΛpos) (le_of_lt hkH) (by norm_num)
    have hΛpow : 0 < Λ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hΛpos _
    have hkw : 0 < periodicFrequencyWeight k ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one
        (one_le_periodicFrequencyWeight k)) _
    exact (inv_le_inv₀ hkw hΛpow).2 hpow
  calc
    (∑ k ∈ highFrequencySet S Λ,
        (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) ≤
        ∑ k ∈ highFrequencySet S Λ, (Λ ^ (1 / 2 : ℝ))⁻¹ := by
      exact Finset.sum_le_sum (fun k hk => hterm k hk)
    _ = (highFrequencySet S Λ).card * (Λ ^ (1 / 2 : ℝ))⁻¹ := by
      simp [nsmul_eq_mul]

/- The preceding arithmetic estimate plugs directly into the weighted finite
critical bridge.  This is a genuine high-frequency packet estimate, with the
finite cardinality factor displayed rather than hidden in an unnamed
constant. -/
theorem cubeIntegral_norm_high_periodicFourier_sum_pow_three_le
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k)
        (highFrequencySet S Λ) x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt ((highFrequencySet S Λ).card * (Λ ^ (1 / 2 : ℝ))⁻¹) *
        periodicSobolevNorm (1 / 2 : ℝ) f) ^ (3 : ℕ) := by
  let H := highFrequencySet S Λ
  let A : ℝ := ∑ k ∈ H, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹
  let B : ℝ := H.card * (Λ ^ (1 / 2 : ℝ))⁻¹
  have hAB : A ≤ B := by
    dsimp [A, B, H]
    exact highFrequency_reciprocalHalfWeight_le_card_mul S hΛ
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun k _ => inv_nonneg.mpr (Real.rpow_nonneg
      ((one_le_periodicFrequencyWeight k).trans' zero_le_one) _))
  have hB : 0 ≤ B := le_trans hA hAB
  have hsqrt : Real.sqrt A ≤ Real.sqrt B := Real.sqrt_le_sqrt hAB
  have hmul : Real.sqrt A * periodicSobolevNorm (1 / 2 : ℝ) f ≤
      Real.sqrt B * periodicSobolevNorm (1 / 2 : ℝ) f := by
    exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
  have hbase := cubeIntegral_norm_fin_periodicFourier_sum_pow_three_le_of_periodicHalfWeight
    hf hp H
  have hpw := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)) hmul 3
  change cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k) H x‖ ^ (3 : ℕ)) ≤
    (Real.sqrt B * periodicSobolevNorm (1 / 2 : ℝ) f) ^ (3 : ℕ)
  exact hbase.trans hpw

end NSFormalization.Paper1
