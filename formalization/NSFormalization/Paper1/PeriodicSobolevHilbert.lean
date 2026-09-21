import NSFormalization.Paper1.PeriodicSobolev

/-! Actual weighted ℓ² representatives for the periodic Sobolev norm.
The norm is a genuine Hilbert norm on the Fourier data, not a declared surrogate. -/
noncomputable section
namespace NSFormalization.Paper1
open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal BigOperators

 theorem periodicFrequencyWeight_eq (k : PeriodicFrequency) :
    periodicFrequencyWeight k = 1 + (2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  unfold periodicFrequencyWeight
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [norm_mul, Complex.norm_intCast, Complex.norm_I, mul_one, mul_pow, sq_abs]
  norm_num [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

 theorem norm_periodicWeightedCoeff_sq (s : ℝ) (f : Space → ℂ) (k : PeriodicFrequency) :
    ‖periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff f k‖ ^ 2 =
      periodicFrequencyWeight k ^ s * ‖periodicFourierCoeff f k‖ ^ 2 := by
  have hw : 0 ≤ periodicFrequencyWeight k := (one_le_periodicFrequencyWeight k).trans' zero_le_one
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hw _), mul_pow,
    ← Real.rpow_mul_natCast hw]
  simp

/-- Weighted Fourier coefficients of the actual physical field, in complete ℓ². -/
def periodicWeightedFourierLp (s : ℝ) (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (hp : UnitPeriods f) (hs : s ≤ 1) : lp (fun _ : PeriodicFrequency => ℂ) 2 :=
  ⟨fun k => periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff f k,
    memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_periodicWeightedCoeff_sq] using
        summable_periodicSobolev hf hp hs)⟩

 theorem norm_periodicWeightedFourierLp (s : ℝ) (f : Space → ℂ) (hf : ContDiff ℝ 1 f)
    (hp : UnitPeriods f) (hs : s ≤ 1) :
    ‖periodicWeightedFourierLp s f hf hp hs‖ = periodicSobolevNorm s f := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  change (∑' k, ‖periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff f k‖ ^ 2) ^ (1 / (2 : ℝ)) = _
  simp_rw [norm_periodicWeightedCoeff_sq]
  rw [← Real.sqrt_eq_rpow]
  rfl

 theorem periodicSobolevNorm_interpolation {f : Space → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : UnitPeriods f) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    periodicSobolevNorm s f ≤
      (Real.sqrt (cubeIntegral (fun x => ‖f x‖ ^ 2))) ^ (1 - s) *
        (Real.sqrt (periodicH1Energy f)) ^ s := by
  have hA : 0 ≤ cubeIntegral (fun x => ‖f x‖ ^ 2) := cubeIntegral_nonneg (fun x => sq_nonneg _)
  have hB : 0 ≤ periodicH1Energy f := by
    unfold periodicH1Energy
    exact add_nonneg hA (Finset.sum_nonneg (fun i hi => cubeIntegral_nonneg (fun x => sq_nonneg _)))
  have hh := Real.sqrt_le_sqrt (periodicSobolevSq_interpolation hf hp hs0 hs1)
  change periodicSobolevNorm s f ≤ _ at hh
  rw [Real.sqrt_mul (Real.rpow_nonneg hA _)] at hh
  have hsqrt (x r : ℝ) (hx : 0 ≤ x) : Real.sqrt (x ^ r) = Real.sqrt x ^ r := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    convert Real.rpow_div_two_eq_sqrt r hx using 1 <;> ring
  simpa only [hsqrt _ _ hA, hsqrt _ _ hB] using hh

end NSFormalization.Paper1
