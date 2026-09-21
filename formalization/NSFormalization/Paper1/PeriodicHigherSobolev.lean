import NSFormalization.Paper1.PeriodicSobolev
import NavierStokes.PeriodicUniqueness

/-!
# Actual periodic H2 energy and summability

The physical field remains a `C²` unit-periodic function on Euclidean
three-space.  Parseval and the previously proved Fourier formula for actual
coordinate derivatives imply summability at order two.  The exact Bessel
energy is the value energy plus twice the first-derivative energy plus the
sum over all ordered second coordinate derivatives.  No spectral summability
or Fourier reconstruction hypothesis is imposed on the input field.
-/

noncomputable section

namespace NSFormalization.Paper1

open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal BigOperators

/-- A coordinate derivative of a `C²` field is `C¹`. -/
theorem spatialPartial_contDiff_one_of_two {f : Space → ℂ}
    (hf : ContDiff ℝ 2 f) (i : Fin 3) : ContDiff ℝ 1 (spatialPartial i f) :=
  (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

/-- The physical order-two Bessel energy with all ordered second partials. -/
def periodicH2Energy (f : Space → ℂ) : ℝ :=
  cubeIntegral (fun x => ‖f x‖ ^ 2) +
    2 * ∑ i : Fin 3, cubeIntegral (fun x => ‖spatialPartial i f x‖ ^ 2) +
    ∑ i : Fin 3, ∑ j : Fin 3,
      cubeIntegral (fun x => ‖spatialPartial j (spatialPartial i f) x‖ ^ 2)

theorem periodicH2Energy_eq_h1_add_partials (f : Space → ℂ) :
    periodicH2Energy f = periodicH1Energy f +
      ∑ i : Fin 3, periodicH1Energy (spatialPartial i f) := by
  simp only [periodicH2Energy, periodicH1Energy, Finset.sum_add_distrib]
  ring

/-- Parseval at order two for the actual `C²` periodic field and its actual
first and second coordinate derivatives, in the unit-period angular convention. -/
theorem hasSum_periodicH2 {f : Space → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : UnitPeriods f) :
    HasSum (fun k => periodicFrequencyWeight k ^ (2 : ℝ) *
      ‖periodicFourierCoeff f k‖ ^ 2) (periodicH2Energy f) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd (i : Fin 3) := hasSum_periodicH1
    (spatialPartial_contDiff_one_of_two hf i)
    (NavierStokes.PeriodicUniqueness.spatial_partial_periodic hp i)
  have hds : HasSum (fun k => ∑ i : Fin 3,
      periodicFrequencyWeight k * ‖periodicFourierCoeff (spatialPartial i f) k‖ ^ 2)
      (∑ i : Fin 3, periodicH1Energy (spatialPartial i f)) :=
    hasSum_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hd i)
  rw [periodicH2Energy_eq_h1_add_partials]
  convert (hasSum_periodicH1 hf1 hp).add hds using 1
  ext k
  unfold periodicFrequencyWeight
  simp only [Real.rpow_two, periodicFourierCoeff_spatialPartial hf1 hp,
    norm_mul, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The order-two weighted Fourier energy is genuinely summable. -/
theorem summable_periodicSobolev_two {f : Space → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : UnitPeriods f) :
    Summable (fun k => periodicFrequencyWeight k ^ (2 : ℝ) *
      ‖periodicFourierCoeff f k‖ ^ 2) := (hasSum_periodicH2 hf hp).summable

/-- The actual periodic H2 spectral energy equals the physical derivative energy. -/
theorem periodicSobolevSq_two {f : Space → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : UnitPeriods f) : periodicSobolevSq 2 f = periodicH2Energy f :=
  (hasSum_periodicH2 hf hp).tsum_eq

/-- All real orders at most two are summable on the same `C²` periodic field. -/
theorem summable_periodicSobolev_of_le_two {f : Space → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : UnitPeriods f) {s : ℝ} (hs : s ≤ 2) :
    Summable (fun k => periodicFrequencyWeight k ^ s *
      ‖periodicFourierCoeff f k‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg
    (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) s)
    (sq_nonneg _)) ?_ (summable_periodicSobolev_two hf hp)
  intro k
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (one_le_periodicFrequencyWeight k) hs)
    (sq_nonneg _)

/-- An actual coordinate derivative loses one finite differentiability order. -/
theorem spatialPartial_contDiff_pred {n : ℕ} {f : Space → ℂ}
    (hf : ContDiff ℝ (n + 1) f) (i : Fin 3) :
    ContDiff ℝ n (spatialPartial i f) :=
  (hf.fderiv_right (by norm_cast)).clm_apply contDiff_const

/-- Recursive physical Bessel energy.  Each step retains the preceding
energy and adds the preceding energy of every actual coordinate derivative. -/
def periodicIntegerEnergy : ℕ → (Space → ℂ) → ℝ
  | 0, f => cubeIntegral (fun x => ‖f x‖ ^ 2)
  | n + 1, f => periodicIntegerEnergy n f +
      ∑ i : Fin 3, periodicIntegerEnergy n (spatialPartial i f)

@[simp] theorem periodicIntegerEnergy_one (f : Space → ℂ) :
    periodicIntegerEnergy 1 f = periodicH1Energy f := rfl

@[simp] theorem periodicIntegerEnergy_two (f : Space → ℂ) :
    periodicIntegerEnergy 2 f = periodicH2Energy f := by
  change periodicIntegerEnergy 1 f +
    ∑ i : Fin 3, periodicIntegerEnergy 1 (spatialPartial i f) = _
  simpa only [periodicIntegerEnergy_one] using
    (periodicH2Energy_eq_h1_add_partials f).symm

/-- Integer-order Parseval follows by induction on actual coordinate
derivatives.  The field has precisely the finite smoothness order required. -/
theorem hasSum_periodicIntegerEnergy (n : ℕ) {f : Space → ℂ}
    (hf : ContDiff ℝ n f) (hp : UnitPeriods f) :
    HasSum (fun k => periodicFrequencyWeight k ^ n *
      ‖periodicFourierCoeff f k‖ ^ 2) (periodicIntegerEnergy n f) := by
  induction n generalizing f with
  | zero =>
      simpa only [periodicIntegerEnergy, pow_zero, one_mul] using
        hasSum_sq_periodicFourierCoeff f hf.continuous
  | succ n ih =>
      have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast; omega)
      have hfn : ContDiff ℝ n f := hf.of_le (by norm_cast; omega)
      have hd (i : Fin 3) := ih (spatialPartial_contDiff_pred hf i)
        (NavierStokes.PeriodicUniqueness.spatial_partial_periodic hp i)
      have hds : HasSum (fun k => ∑ i : Fin 3,
          periodicFrequencyWeight k ^ n *
            ‖periodicFourierCoeff (spatialPartial i f) k‖ ^ 2)
          (∑ i : Fin 3, periodicIntegerEnergy n (spatialPartial i f)) :=
        hasSum_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hd i)
      change HasSum _ (periodicIntegerEnergy n f +
        ∑ i : Fin 3, periodicIntegerEnergy n (spatialPartial i f))
      convert (ih hfn hp).add hds using 1
      ext k
      rw [pow_succ]
      unfold periodicFrequencyWeight
      simp only [periodicFourierCoeff_spatialPartial hf1 hp, norm_mul, mul_pow,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Every finite-order Bessel norm of the actual periodic field is summable
under the matching `C^n` regularity hypothesis. -/
theorem summable_periodicSobolev_nat (n : ℕ) {f : Space → ℂ}
    (hf : ContDiff ℝ n f) (hp : UnitPeriods f) :
    Summable (fun k => periodicFrequencyWeight k ^ (n : ℝ) *
      ‖periodicFourierCoeff f k‖ ^ 2) := by
  simpa only [Real.rpow_natCast] using (hasSum_periodicIntegerEnergy n hf hp).summable

/-- The recursive physical energy equals the already defined spectral energy. -/
theorem periodicSobolevSq_nat (n : ℕ) {f : Space → ℂ}
    (hf : ContDiff ℝ n f) (hp : UnitPeriods f) :
    periodicSobolevSq n f = periodicIntegerEnergy n f := by
  simpa only [periodicSobolevSq, Real.rpow_natCast] using
    (hasSum_periodicIntegerEnergy n hf hp).tsum_eq

/-- Real-order summability follows from any dominating finite smoothness order. -/
theorem summable_periodicSobolev_of_le_nat (n : ℕ) {f : Space → ℂ}
    (hf : ContDiff ℝ n f) (hp : UnitPeriods f) {s : ℝ} (hs : s ≤ n) :
    Summable (fun k => periodicFrequencyWeight k ^ s *
      ‖periodicFourierCoeff f k‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg
    (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) s)
    (sq_nonneg _)) ?_ (summable_periodicSobolev_nat n hf hp)
  intro k
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (one_le_periodicFrequencyWeight k) hs)
    (sq_nonneg _)

/-- The physical `H²` energy controls a genuine norm, with no default-zero
infinite sum involved in its definition. -/
theorem periodicSobolevNorm_two {f : Space → ℂ} (hf : ContDiff ℝ 2 f)
    (hp : UnitPeriods f) :
    periodicSobolevNorm 2 f = Real.sqrt (periodicH2Energy f) := by
  rw [periodicSobolevNorm, periodicSobolevSq_two hf hp]

end NSFormalization.Paper1
