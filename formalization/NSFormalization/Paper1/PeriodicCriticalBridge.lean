import NSFormalization.Paper1.PeriodicFiniteCriticalInterface

/-!
# Weighted finite-frequency bridge toward the periodic critical estimate

The elementary coefficient `ℓ¹` step can be paired with the half-order
Fourier energy using the reciprocal frequency weight.  This improves the raw
`√(card S)` loss to the exact finite multiplier
`√(∑_{k∈S} weight(k)⁻¹)`.  The multiplier is the finite-dimensional shadow of
the endpoint obstruction: controlling it uniformly over expanding spectra is
precisely an additional analytic estimate, and is not assumed here.
-/
noncomputable section
namespace NSFormalization.Paper1
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal

theorem finite_coeff_l1_le_weightedEnergy_mul_invWeight
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency)
    (w : PeriodicFrequency → ℝ) (hw : ∀ k, 0 < w k) :
    (∑ k ∈ S, ‖c k‖) ≤
      Real.sqrt (∑ k ∈ S, w k * ‖c k‖ ^ 2) *
        Real.sqrt (∑ k ∈ S, (w k)⁻¹) := by
  let f : PeriodicFrequency → ℝ := fun k => Real.sqrt (w k) * ‖c k‖
  let g : PeriodicFrequency → ℝ := fun k => (Real.sqrt (w k))⁻¹
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S f g
  have hfg : ∀ k ∈ S, f k * g k = ‖c k‖ := by
    intro k hk
    dsimp [f, g]
    have hs : (Real.sqrt (w k)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw k))
    field_simp
  have hf : (∑ k ∈ S, f k ^ 2) = ∑ k ∈ S, w k * ‖c k‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hw k))]
  have hg : (∑ k ∈ S, g k ^ 2) = ∑ k ∈ S, (w k)⁻¹ := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [g]
    rw [inv_pow, Real.sq_sqrt (le_of_lt (hw k))]
  calc
    (∑ k ∈ S, ‖c k‖) = ∑ k ∈ S, f k * g k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (hfg k hk).symm
    _ ≤ Real.sqrt (∑ k ∈ S, f k ^ 2) * Real.sqrt (∑ k ∈ S, g k ^ 2) := hcs
    _ = Real.sqrt (∑ k ∈ S, w k * ‖c k‖ ^ 2) *
        Real.sqrt (∑ k ∈ S, (w k)⁻¹) := by rw [hf, hg]

theorem cubeIntegral_norm_fin_fourier_sum_pow_three_le_of_weightedEnergy
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency)
    (w : PeriodicFrequency → ℝ) (hw : ∀ k, 0 < w k) :
    cubeIntegral (fun x => ‖finitePeriodicFourierSum c S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt (∑ k ∈ S, (w k)⁻¹) *
        Real.sqrt (∑ k ∈ S, w k * ‖c k‖ ^ 2)) ^ (3 : ℕ) := by
  have hl1 := finite_coeff_l1_le_weightedEnergy_mul_invWeight c S w hw
  have hbase := cubeIntegral_norm_fin_fourier_sum_pow_three_le c S
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ∑ k ∈ S, ‖c k‖) hl1 3
  have hcomm : Real.sqrt (∑ k ∈ S, w k * ‖c k‖ ^ 2) *
      Real.sqrt (∑ k ∈ S, (w k)⁻¹) =
      Real.sqrt (∑ k ∈ S, (w k)⁻¹) *
      Real.sqrt (∑ k ∈ S, w k * ‖c k‖ ^ 2) := by ring
  rw [hcomm] at hp
  exact hbase.trans hp

theorem cubeIntegral_norm_fin_fourier_sum_pow_three_le_of_periodicHalfWeight
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency) :
    cubeIntegral (fun x => ‖finitePeriodicFourierSum c S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt (∑ k ∈ S, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) *
        Real.sqrt (∑ k ∈ S, periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
          ‖c k‖ ^ 2)) ^ (3 : ℕ) := by
  apply cubeIntegral_norm_fin_fourier_sum_pow_three_le_of_weightedEnergy c S
  intro k
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one
    (one_le_periodicFrequencyWeight k)) _

theorem cubeIntegral_norm_fin_periodicFourier_sum_pow_three_le_of_periodicHalfWeight
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) :
    cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k) S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt (∑ k ∈ S,
          (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) *
        periodicSobolevNorm (1 / 2 : ℝ) f) ^ (3 : ℕ) := by
  have hbase := cubeIntegral_norm_fin_fourier_sum_pow_three_le_of_periodicHalfWeight
    (fun k => periodicFourierCoeff f k) S
  have henergy : (∑ k ∈ S, periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
      ‖periodicFourierCoeff f k‖ ^ 2) ≤ periodicSobolevSq (1 / 2 : ℝ) f := by
    have hsum : Summable (fun k : PeriodicFrequency =>
        periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
          ‖periodicFourierCoeff f k‖ ^ 2) :=
      summable_periodicSobolev hf hp (by norm_num)
    exact Summable.sum_le_tsum S
      (fun k _ => mul_nonneg
        (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) _)
        (sq_nonneg _)) hsum
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hmul :
      Real.sqrt (∑ k ∈ S, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) *
          Real.sqrt (∑ k ∈ S, periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
            ‖periodicFourierCoeff f k‖ ^ 2) ≤
        Real.sqrt (∑ k ∈ S, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) *
          Real.sqrt (periodicSobolevSq (1 / 2 : ℝ) f) := by
    exact mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
      Real.sqrt (∑ k ∈ S, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) *
        Real.sqrt (∑ k ∈ S, periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
          ‖periodicFourierCoeff f k‖ ^ 2)) hmul 3
  change cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k) S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt (∑ k ∈ S, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) *
        Real.sqrt (periodicSobolevSq (1 / 2 : ℝ) f)) ^ (3 : ℕ)
  exact hbase.trans hp

end NSFormalization.Paper1
