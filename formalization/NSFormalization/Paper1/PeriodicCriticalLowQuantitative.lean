import NSFormalization.Paper1.PeriodicCriticalLowHigh
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-!
# Quantitative low-frequency control at a finite threshold

For modes whose Bessel weight is at most `Λ`, the homogeneous half-order
energy is bounded by `Λ^(1/2)` times the unweighted coefficient energy.  This
is an elementary finite-band estimate.  Combined with the existing finite
Fourier `L^3` estimate it gives an explicit threshold-dependent bound; it does
not assert a uniform `H^(1/2) → L^3` estimate.
-/
noncomputable section
namespace NSFormalization.Paper1

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal

/-- On the low-frequency set, angular frequency is bounded by `sqrt Λ`.
The hypothesis `1 ≤ Λ` makes the comparison with the inhomogeneous Bessel
weight immediate, including the zero mode. -/
theorem periodicAngularMagnitude_le_sqrt_threshold_of_mem_low
    (S : Finset PeriodicFrequency) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {k : PeriodicFrequency} (hk : k ∈ lowFrequencySet S Λ) :
    periodicAngularMagnitude k ≤ Real.sqrt Λ := by
  have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
  have hkw : periodicFrequencyWeight k ≤ Λ := (Finset.mem_filter.mp hk).2
  have hΛ0 : 0 ≤ Λ := by linarith
  have harg : periodicFrequencyWeight k - 1 ≤ Λ := by linarith
  unfold periodicAngularMagnitude
  apply Real.sqrt_le_sqrt
  nlinarith [harg, hΛ0]

/-- Finite low-frequency homogeneous half-energy is controlled by the
threshold and the finite unweighted coefficient energy. -/
theorem homogeneousHalfEnergy_low_le_sqrt_threshold_mul_l2
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    homogeneousHalfEnergy c (lowFrequencySet S Λ) ≤
      Real.sqrt Λ * (∑ k ∈ lowFrequencySet S Λ, ‖c k‖ ^ 2) := by
  have hterm : ∀ k ∈ lowFrequencySet S Λ,
      periodicAngularMagnitude k * ‖c k‖ ^ 2 ≤
        Real.sqrt Λ * ‖c k‖ ^ 2 := by
    intro k hk
    exact mul_le_mul_of_nonneg_right
      (periodicAngularMagnitude_le_sqrt_threshold_of_mem_low S hΛ hk)
      (sq_nonneg _)
  unfold homogeneousHalfEnergy
  calc
    (∑ k ∈ lowFrequencySet S Λ,
        periodicAngularMagnitude k * ‖c k‖ ^ 2) ≤
        ∑ k ∈ lowFrequencySet S Λ, Real.sqrt Λ * ‖c k‖ ^ 2 := by
      exact Finset.sum_le_sum (fun k hk => hterm k hk)
    _ = Real.sqrt Λ * (∑ k ∈ lowFrequencySet S Λ, ‖c k‖ ^ 2) := by
      rw [Finset.mul_sum]

/-- The preceding finite-band estimate for Fourier coefficients of a smooth
periodic field, with the complete `H^0` spectral square on the right. -/
theorem homogeneousHalfEnergy_low_periodicFourier_le
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    homogeneousHalfEnergy (fun k => periodicFourierCoeff f k)
        (lowFrequencySet S Λ) ≤
      Real.sqrt Λ * periodicSobolevSq 0 f := by
  have hfinite := homogeneousHalfEnergy_low_le_sqrt_threshold_mul_l2
    (fun k => periodicFourierCoeff f k) S hΛ
  have hsum : (∑ k ∈ lowFrequencySet S Λ,
      ‖periodicFourierCoeff f k‖ ^ 2) ≤
      ∑' k : PeriodicFrequency, ‖periodicFourierCoeff f k‖ ^ 2 := by
    have hs : Summable (fun k : PeriodicFrequency =>
        periodicFrequencyWeight k ^ (0 : ℝ) *
          ‖periodicFourierCoeff f k‖ ^ 2) :=
      summable_periodicSobolev hf hp (by norm_num)
    have hs0 : Summable (fun k : PeriodicFrequency =>
        ‖periodicFourierCoeff f k‖ ^ 2) := by
      simpa only [Real.rpow_zero, one_mul] using hs
    have hle := Summable.sum_le_tsum (lowFrequencySet S Λ)
      (fun k _ => sq_nonneg (‖periodicFourierCoeff f k‖)) hs0
    simpa only [Real.rpow_zero, one_mul] using hle
  have hmul := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg Λ)
  calc
    homogeneousHalfEnergy (fun k => periodicFourierCoeff f k)
        (lowFrequencySet S Λ) ≤
        Real.sqrt Λ * (∑ k ∈ lowFrequencySet S Λ,
          ‖periodicFourierCoeff f k‖ ^ 2) := hfinite
    _ ≤ Real.sqrt Λ * (∑' k : PeriodicFrequency,
          ‖periodicFourierCoeff f k‖ ^ 2) := hmul
    _ = Real.sqrt Λ * periodicSobolevSq 0 f := by
      simp only [periodicSobolevSq, Real.rpow_zero, one_mul]

/-- Explicit `Λ`-dependent low-frequency cubic estimate.  The cardinality of
 the retained packet is shown explicitly, and the `H^0` spectral energy is
 kept as the controlling norm. -/
theorem cubeIntegral_norm_low_periodicFourier_sum_pow_three_le_of_threshold
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hmean : cubeIntegral f = 0) :
    cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k)
        (lowFrequencySet S Λ) x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt (lowFrequencySet S Λ).card *
        Real.sqrt (Real.sqrt Λ * periodicSobolevSq 0 f)) ^ (3 : ℕ) := by
  have hbase := cubeIntegral_norm_fin_fourier_sum_pow_three_le_of_meanZero
    (fun k => periodicFourierCoeff f k) (lowFrequencySet S Λ)
    (periodicFourierCoeff_zero_eq_zero_iff f |>.mpr hmean)
  have henergy := homogeneousHalfEnergy_low_periodicFourier_le hf hp S hΛ
  have hsqrt := Real.sqrt_le_sqrt henergy
  have hmul :
      Real.sqrt (lowFrequencySet S Λ).card *
          Real.sqrt (homogeneousHalfEnergy
            (fun k => periodicFourierCoeff f k) (lowFrequencySet S Λ)) ≤
        Real.sqrt (lowFrequencySet S Λ).card *
          Real.sqrt (Real.sqrt Λ * periodicSobolevSq 0 f) := by
    exact mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
      Real.sqrt (lowFrequencySet S Λ).card *
        Real.sqrt (homogeneousHalfEnergy
          (fun k => periodicFourierCoeff f k) (lowFrequencySet S Λ))) hmul 3
  exact hbase.trans hp

/-- A finite integer-frequency box in three dimensions. -/
def periodicFrequencyBox (R : ℕ) : Finset PeriodicFrequency :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(R : ℤ)) (R : ℤ))

theorem card_periodicFrequencyBox (R : ℕ) :
    (periodicFrequencyBox R).card = (2 * R + 1) ^ 3 := by
  simp [periodicFrequencyBox, Fintype.card_piFinset, Int.card_Icc]
  omega

/-- Each integer coordinate square is bounded by the angular Bessel weight. -/
theorem periodicFrequency_coordinate_sq_le_weight
    (k : PeriodicFrequency) (i : Fin 3) :
    (k i : ℝ) ^ 2 ≤ periodicFrequencyWeight k := by
  rw [periodicFrequencyWeight_eq]
  have hsingle : (k i : ℝ) ^ 2 ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
  have hsum : 0 ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 := by positivity
  have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by
    have h := Real.pi_gt_three
    nlinarith [sq_nonneg Real.pi]
  have hmul := mul_le_mul_of_nonneg_right hpi hsum
  nlinarith

/-- A weight cutoff lies in a finite coordinate box, independently of the
original finite spectrum. -/
theorem lowFrequencySet_subset_frequencyBox
    (S : Finset PeriodicFrequency) {Λ : ℝ} {R : ℕ}
    (hΛR : Λ ≤ (R : ℝ) ^ 2) :
    lowFrequencySet S Λ ⊆ periodicFrequencyBox R := by
  intro k hk
  apply Fintype.mem_piFinset.mpr
  intro i
  have hkw := (Finset.mem_filter.mp hk).2
  have hsq : (k i : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 :=
    (periodicFrequency_coordinate_sq_le_weight k i).trans (hkw.trans hΛR)
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hlo : -(R : ℝ) ≤ k i := by nlinarith
  have hhi : (k i : ℝ) ≤ R := by nlinarith
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- Low-frequency counting with an explicit radius bound and no dependence
on the size of the original finite spectrum. -/
theorem card_lowFrequencySet_le_box
    (S : Finset PeriodicFrequency) {Λ : ℝ} {R : ℕ}
    (hΛR : Λ ≤ (R : ℝ) ^ 2) :
    (lowFrequencySet S Λ).card ≤ (2 * R + 1) ^ 3 := by
  simpa only [card_periodicFrequencyBox] using
    Finset.card_le_card (lowFrequencySet_subset_frequencyBox S hΛR)

/-- The low-band cubic estimate can replace the support cardinality by an
explicit integer-radius box whenever `Λ ≤ R²`. -/
theorem cubeIntegral_norm_low_periodicFourier_sum_pow_three_le_of_radius
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) {Λ : ℝ} {R : ℕ} (hΛ : 1 ≤ Λ)
    (hΛR : Λ ≤ (R : ℝ) ^ 2) (hmean : cubeIntegral f = 0) :
    cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k)
        (lowFrequencySet S Λ) x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt ((2 * R + 1) ^ 3) *
        Real.sqrt (Real.sqrt Λ * periodicSobolevSq 0 f)) ^ (3 : ℕ) := by
  have hbase := cubeIntegral_norm_low_periodicFourier_sum_pow_three_le_of_threshold
    hf hp S hΛ hmean
  have hcard := card_lowFrequencySet_le_box S hΛR
  have hcardR : (lowFrequencySet S Λ).card ≤ ((2 * R + 1) ^ 3 : ℝ) := by
    exact_mod_cast hcard
  have hsqrt := Real.sqrt_le_sqrt hcardR
  have hmul := mul_le_mul_of_nonneg_right hsqrt
    (Real.sqrt_nonneg (Real.sqrt Λ * periodicSobolevSq 0 f))
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
      Real.sqrt (lowFrequencySet S Λ).card *
        Real.sqrt (Real.sqrt Λ * periodicSobolevSq 0 f)) hmul 3
  exact hbase.trans hp

end NSFormalization.Paper1
