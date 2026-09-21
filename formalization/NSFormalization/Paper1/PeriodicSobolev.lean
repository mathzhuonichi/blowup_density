import NSFormalization.Paper1.PeriodicFourierDerivative
import NSFormalization.Paper1.SpectralInterpolation

/-! Actual periodic Fourier Sobolev norms, their physical H0/H1 identities,
monotonicity, and interpolation. All sums used below are proved summable. -/
noncomputable section
namespace NSFormalization.Paper1
open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal BigOperators

/-- Unit-period angular Bessel weight `1 + |2πk|²`. -/
def periodicFrequencyWeight (k : PeriodicFrequency) : ℝ :=
  1 + ∑ i : Fin 3, ‖(2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)‖ ^ 2

theorem one_le_periodicFrequencyWeight (k : PeriodicFrequency) : 1 ≤ periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  have h := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    sq_nonneg ‖(2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)‖)
  linarith

def periodicSobolevSq (s : ℝ) (f : Space → ℂ) : ℝ :=
  ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ s * ‖periodicFourierCoeff f k‖ ^ 2

def periodicSobolevNorm (s : ℝ) (f : Space → ℂ) : ℝ := Real.sqrt (periodicSobolevSq s f)

/-- Physical H1 energy in the source cube integration convention. -/
def periodicH1Energy (f : Space → ℂ) : ℝ :=
  cubeIntegral (fun x => ‖f x‖ ^ 2) +
    ∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i f x‖ ^ 2)

 theorem hasSum_periodicH1 {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f) :
    HasSum (fun k => periodicFrequencyWeight k * ‖periodicFourierCoeff f k‖ ^ 2)
      (periodicH1Energy f) := by
  unfold periodicH1Energy
  have hd (i : Fin 3) := hasSum_sq_periodicFourierCoeff (spatialPartial i f) (continuous_partial hf i)
  have hds : HasSum (fun k => ∑ i : Fin 3, ‖periodicFourierCoeff (spatialPartial i f) k‖ ^ 2)
      (∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i f x‖ ^ 2)) := by
    exact hasSum_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hd i)
  have h := (hasSum_sq_periodicFourierCoeff f hf.continuous).add hds
  convert h using 1
  ext k
  simp only [periodicFrequencyWeight, periodicFourierCoeff_spatialPartial hf hp,
    norm_mul, mul_pow, add_mul, one_mul, Finset.sum_mul]

 theorem periodicSobolevSq_zero {f : Space → ℂ} (hf : Continuous f) :
    periodicSobolevSq 0 f = cubeIntegral (fun x => ‖f x‖ ^ 2) := by
  simpa [periodicSobolevSq] using (hasSum_sq_periodicFourierCoeff f hf).tsum_eq

 theorem periodicSobolevSq_one {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f) :
    periodicSobolevSq 1 f = periodicH1Energy f := by
  simpa [periodicSobolevSq] using (hasSum_periodicH1 hf hp).tsum_eq

/-- The weighted Fourier energy is actually summable at every order ≤1. -/
theorem summable_periodicSobolev {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    {s : ℝ} (hs : s ≤ 1) :
    Summable (fun k => periodicFrequencyWeight k ^ s * ‖periodicFourierCoeff f k‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg
    ((one_le_periodicFrequencyWeight k).trans' zero_le_one) s) (sq_nonneg _)) ?_
    (hasSum_periodicH1 hf hp).summable
  intro k
  apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (one_le_periodicFrequencyWeight k) hs

/-- Monotonicity at actual smooth inputs; summability prevents default-zero tsum artifacts. -/
theorem periodicSobolevSq_mono {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    {s r : ℝ} (hsr : s ≤ r) (hr : r ≤ 1) : periodicSobolevSq s f ≤ periodicSobolevSq r f := by
  unfold periodicSobolevSq
  apply Summable.tsum_le_tsum ?_ (summable_periodicSobolev hf hp (hsr.trans hr))
    (summable_periodicSobolev hf hp hr)
  intro k
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (one_le_periodicFrequencyWeight k) hsr) (sq_nonneg _)

 theorem periodicSobolevNorm_mono {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    {s r : ℝ} (hsr : s ≤ r) (hr : r ≤ 1) : periodicSobolevNorm s f ≤ periodicSobolevNorm r f :=
  Real.sqrt_le_sqrt (periodicSobolevSq_mono hf hp hsr hr)

/-- H0--H1 spectral interpolation, in the original physical cube energy convention. -/
theorem periodicSobolevSq_interpolation {f : Space → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : UnitPeriods f) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    periodicSobolevSq s f ≤
      (cubeIntegral (fun x => ‖f x‖ ^ 2)) ^ (1 - s) * (periodicH1Energy f) ^ s := by
  rcases hs0.eq_or_lt with h0 | hs0
  · subst s
    simp [periodicSobolevSq_zero hf.continuous]
  rcases hs1.eq_or_lt with h1 | hs1
  · subst s
    simp [periodicSobolevSq_one hf hp]
  have h := summable_spectral_interpolation
    (fun k : PeriodicFrequency => sq_nonneg ‖periodicFourierCoeff f k‖)
    (fun k => (one_le_periodicFrequencyWeight k).trans' zero_le_one)
    (hasSum_sq_periodicFourierCoeff f hf.continuous).summable
    (hasSum_periodicH1 hf hp).summable hs0 hs1
  simpa only [periodicSobolevSq,
    (hasSum_sq_periodicFourierCoeff f hf.continuous).tsum_eq, (hasSum_periodicH1 hf hp).tsum_eq] using h.2

end NSFormalization.Paper1
