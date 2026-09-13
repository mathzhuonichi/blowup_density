import NSFormalization.Paper1.PeriodicCriticalLowHigh

/-!
# Explicit low/high recombination at the critical interface

This file records the strongest finite statement currently available without
the periodic critical embedding.  The low and high reciprocal multipliers are
kept separately, and then added before taking the cubic bound.  Thus no
cutoff-independent constant is hidden in the statement.
-/
noncomputable section
namespace NSFormalization.Paper1

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal

theorem finite_coeff_l1_periodicFourier_le_low_add_high_weighted
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) (Λ : ℝ) :
    (∑ k ∈ S, ‖periodicFourierCoeff f k‖) ≤
      (Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) +
        Real.sqrt (∑ k ∈ highFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹)) *
        periodicSobolevNorm (1 / 2 : ℝ) f := by
  let w : PeriodicFrequency → ℝ := fun k =>
    periodicFrequencyWeight k ^ (1 / 2 : ℝ)
  have hw : ∀ k, 0 < w k := by
    intro k
    dsimp [w]
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one
      (one_le_periodicFrequencyWeight k)) _
  have hsumL : Summable (fun k : PeriodicFrequency =>
      w k * ‖periodicFourierCoeff f k‖ ^ 2) := by
    simpa [w] using summable_periodicSobolev hf hp (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have henergyL (T : Finset PeriodicFrequency) :
      (∑ k ∈ T, w k * ‖periodicFourierCoeff f k‖ ^ 2) ≤
        periodicSobolevSq (1 / 2 : ℝ) f := by
    exact (Summable.sum_le_tsum T
      (fun k _ => mul_nonneg (le_of_lt (hw k)) (sq_nonneg _)) hsumL)
  have hL := finite_coeff_l1_le_weightedEnergy_mul_invWeight
    (fun k => periodicFourierCoeff f k) (lowFrequencySet S Λ) w hw
  have hH := finite_coeff_l1_le_weightedEnergy_mul_invWeight
    (fun k => periodicFourierCoeff f k) (highFrequencySet S Λ) w hw
  have hL' : (∑ k ∈ lowFrequencySet S Λ, ‖periodicFourierCoeff f k‖) ≤
      Real.sqrt (periodicSobolevSq (1 / 2 : ℝ) f) *
        Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) := by
    have h := hL
    have hs := Real.sqrt_le_sqrt (henergyL (lowFrequencySet S Λ))
    have hm := mul_le_mul_of_nonneg_right hs
      (Real.sqrt_nonneg (∑ k ∈ lowFrequencySet S Λ, (w k)⁻¹))
    simpa [w, mul_comm] using h.trans hm
  have hH' : (∑ k ∈ highFrequencySet S Λ, ‖periodicFourierCoeff f k‖) ≤
      Real.sqrt (periodicSobolevSq (1 / 2 : ℝ) f) *
        Real.sqrt (∑ k ∈ highFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) := by
    have h := hH
    have hs := Real.sqrt_le_sqrt (henergyL (highFrequencySet S Λ))
    have hm := mul_le_mul_of_nonneg_right hs
      (Real.sqrt_nonneg (∑ k ∈ highFrequencySet S Λ, (w k)⁻¹))
    simpa [w, mul_comm] using h.trans hm
  have hsplit := sum_split_low_high
    (fun k : PeriodicFrequency => ‖periodicFourierCoeff f k‖) S Λ
  rw [hsplit]
  have hsum := add_le_add hL' hH'
  calc
    (∑ k ∈ lowFrequencySet S Λ, ‖periodicFourierCoeff f k‖) +
        ∑ k ∈ highFrequencySet S Λ, ‖periodicFourierCoeff f k‖ ≤
      Real.sqrt (periodicSobolevSq (1 / 2 : ℝ) f) *
          (Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
            (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) +
            Real.sqrt (∑ k ∈ highFrequencySet S Λ,
              (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹)) := by
      simpa [mul_add] using hsum
    _ = (Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) +
        Real.sqrt (∑ k ∈ highFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹)) *
        periodicSobolevNorm (1 / 2 : ℝ) f := by
      unfold periodicSobolevNorm
      ring

theorem cubeIntegral_norm_fin_periodicFourier_sum_pow_three_le_low_add_high
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) (Λ : ℝ) :
    cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k) S x‖ ^ (3 : ℕ)) ≤
      ((Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) +
        Real.sqrt (∑ k ∈ highFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹)) *
        periodicSobolevNorm (1 / 2 : ℝ) f) ^ (3 : ℕ) := by
  have hbase := cubeIntegral_norm_fin_fourier_sum_pow_three_le
    (fun k => periodicFourierCoeff f k) S
  have hl1 := finite_coeff_l1_periodicFourier_le_low_add_high_weighted hf hp S Λ
  have hnonneg : 0 ≤ ∑ k ∈ S, ‖periodicFourierCoeff f k‖ := by positivity
  have hpw := pow_le_pow_left₀ hnonneg hl1 3
  exact hbase.trans hpw

/- The high reciprocal sum can be replaced by the explicit cutoff bound from
`PeriodicCriticalLowHigh`.  This keeps the low-frequency multiplier exact and
exposes the finite cardinality loss on the high packet. -/
theorem finite_coeff_l1_periodicFourier_le_low_plus_high_cardinal
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    (∑ k ∈ S, ‖periodicFourierCoeff f k‖) ≤
      (Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) +
        Real.sqrt ((highFrequencySet S Λ).card *
          (Λ ^ (1 / 2 : ℝ))⁻¹)) *
        periodicSobolevNorm (1 / 2 : ℝ) f := by
  have hbase := finite_coeff_l1_periodicFourier_le_low_add_high_weighted
    hf hp S Λ
  have hrec := highFrequency_reciprocalHalfWeight_le_card_mul S hΛ
  have hsqrt := Real.sqrt_le_sqrt hrec
  have hmul := add_le_add_left hsqrt
    (Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
      (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹))
  have hnorm : 0 ≤ periodicSobolevNorm (1 / 2 : ℝ) f :=
    Real.sqrt_nonneg _
  have hscaled := mul_le_mul_of_nonneg_right hmul hnorm
  have hscaled' :
      (Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) +
        Real.sqrt (∑ k ∈ highFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹)) *
        periodicSobolevNorm (1 / 2 : ℝ) f ≤
      (Real.sqrt (∑ k ∈ lowFrequencySet S Λ,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) +
        Real.sqrt ((highFrequencySet S Λ).card *
          (Λ ^ (1 / 2 : ℝ))⁻¹)) *
        periodicSobolevNorm (1 / 2 : ℝ) f := by
    simpa [add_comm] using hscaled
  exact hbase.trans hscaled'

end NSFormalization.Paper1
