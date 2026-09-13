import NSFormalization.Paper1.PeriodicHigherSobolev
import NSFormalization.Paper1.PeriodicSobolevHilbert

/-!
# All real Sobolev orders for smooth periodic fields

The integer-order Parseval theorem supplies genuine summability at a natural
order above any prescribed real exponent. Comparison of the positive Bessel
weights then gives all real orders, including negative orders. Weighted
Fourier coefficients are actual elements of the complete sequence space `ℓ²`.
-/

noncomputable section
namespace NSFormalization.Paper1

open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal BigOperators

/-- Smooth unit-periodic fields have summable Fourier energy at every real
Sobolev order. There is no spectral summability hypothesis. -/
theorem summable_periodicSobolev_smooth (s : ℝ) {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f) :
    Summable (fun k => periodicFrequencyWeight k ^ s *
      ‖periodicFourierCoeff f k‖ ^ 2) := by
  obtain ⟨n, hn⟩ := exists_nat_ge s
  exact summable_periodicSobolev_of_le_nat n (hf.of_le (by simp)) hp hn

/-- Monotonicity at arbitrary real orders for smooth periodic fields. -/
theorem periodicSobolevSq_mono_smooth {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f) {s r : ℝ} (hsr : s ≤ r) :
    periodicSobolevSq s f ≤ periodicSobolevSq r f := by
  apply Summable.tsum_le_tsum _ (summable_periodicSobolev_smooth s hf hp)
    (summable_periodicSobolev_smooth r hf hp)
  intro k
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (one_le_periodicFrequencyWeight k) hsr)
    (sq_nonneg _)

theorem periodicSobolevNorm_mono_smooth {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f) {s r : ℝ} (hsr : s ≤ r) :
    periodicSobolevNorm s f ≤ periodicSobolevNorm r f :=
  Real.sqrt_le_sqrt (periodicSobolevSq_mono_smooth hf hp hsr)

/-- The actual weighted Fourier representative at any real order. -/
def smoothPeriodicWeightedFourierLp (s : ℝ) (f : Space → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f) :
    lp (fun _ : PeriodicFrequency => ℂ) 2 :=
  ⟨fun k => periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff f k,
    memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_periodicWeightedCoeff_sq]
        using summable_periodicSobolev_smooth s hf hp)⟩

theorem norm_smoothPeriodicWeightedFourierLp (s : ℝ) (f : Space → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f) :
    ‖smoothPeriodicWeightedFourierLp s f hf hp‖ = periodicSobolevNorm s f := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  change (∑' k, ‖periodicFrequencyWeight k ^ (s / 2) •
    periodicFourierCoeff f k‖ ^ 2) ^ (1 / (2 : ℝ)) = _
  simp_rw [norm_periodicWeightedCoeff_sq]
  rw [← Real.sqrt_eq_rpow]
  rfl

/-- Additivity of the actual coefficients follows from integration over the
fixed fundamental cube and requires only continuity. -/
theorem periodicFourierCoeff_add {f g : Space → ℂ}
    (hf : Continuous f) (hg : Continuous g) (k : PeriodicFrequency) :
    periodicFourierCoeff (f + g) k =
      periodicFourierCoeff f k + periodicFourierCoeff g k := by
  simp only [periodicFourierCoeff_eq_cube, Pi.add_apply, mul_add]
  exact integral_add
    (integrable_cube ((periodicCharacter_smooth (-k)).continuous.mul hf))
    (integrable_cube ((periodicCharacter_smooth (-k)).continuous.mul hg))

/-- The finite-regularity scalar triangle inequality already applies to all
orders at most one. -/
theorem periodicSobolevNorm_add_le {f g : Space → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : UnitPeriods f) (hgp : UnitPeriods g) {s : ℝ} (hs : s ≤ 1) :
    periodicSobolevNorm s (f + g) ≤
      periodicSobolevNorm s f + periodicSobolevNorm s g := by
  have hp : UnitPeriods (f + g) := by
    intro x i
    exact congrArg₂ (· + ·) (hfp x i) (hgp x i)
  have he : periodicWeightedFourierLp s (f + g) (hf.add hg) hp hs =
      periodicWeightedFourierLp s f hf hfp hs +
        periodicWeightedFourierLp s g hg hgp hs := by
    apply lp.ext
    funext k
    change periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff (f + g) k =
      periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff f k +
        periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff g k
    rw [periodicFourierCoeff_add hf.continuous hg.continuous, smul_add]
  rw [← norm_periodicWeightedFourierLp s (f + g) (hf.add hg) hp hs, he,
    ← norm_periodicWeightedFourierLp s f hf hfp hs,
    ← norm_periodicWeightedFourierLp s g hg hgp hs]
  exact norm_add_le _ _

/-- Smooth fields satisfy the scalar triangle inequality at every real order. -/
theorem periodicSobolevNorm_add_le_smooth {f g : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : UnitPeriods f) (hgp : UnitPeriods g) (s : ℝ) :
    periodicSobolevNorm s (f + g) ≤
      periodicSobolevNorm s f + periodicSobolevNorm s g := by
  have hp : UnitPeriods (f + g) := by
    intro x i
    exact congrArg₂ (· + ·) (hfp x i) (hgp x i)
  have he : smoothPeriodicWeightedFourierLp s (f + g) (hf.add hg) hp =
      smoothPeriodicWeightedFourierLp s f hf hfp +
        smoothPeriodicWeightedFourierLp s g hg hgp := by
    apply lp.ext
    funext k
    change periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff (f + g) k =
      periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff f k +
        periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff g k
    rw [periodicFourierCoeff_add hf.continuous hg.continuous, smul_add]
  rw [← norm_smoothPeriodicWeightedFourierLp s (f + g) (hf.add hg) hp, he,
    ← norm_smoothPeriodicWeightedFourierLp s f hf hfp,
    ← norm_smoothPeriodicWeightedFourierLp s g hg hgp]
  exact norm_add_le _ _

/-! ### Separation of Fourier modes -/

/-- If the weighted periodic Sobolev square is zero, every Fourier coefficient
vanishes.  Smoothness supplies summability, while positivity of the Bessel
weight allows extraction of each nonnegative summand from the `tsum`. -/
theorem coeff_zero_of_periodicSobolevSq_zero {s : ℝ} {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f)
    (hzero : periodicSobolevSq s f = 0) (k : PeriodicFrequency) :
    periodicFourierCoeff f k = 0 := by
  have hsumm : Summable (fun j : PeriodicFrequency =>
      periodicFrequencyWeight j ^ s * ‖periodicFourierCoeff f j‖ ^ 2) :=
    summable_periodicSobolev_smooth s hf hp
  have hnonneg (j : PeriodicFrequency) : 0 ≤
      periodicFrequencyWeight j ^ s * ‖periodicFourierCoeff f j‖ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg ((one_le_periodicFrequencyWeight j).trans' zero_le_one) s)
      (sq_nonneg _)
  have hterm : periodicFrequencyWeight k ^ s * ‖periodicFourierCoeff f k‖ ^ 2 ≤ 0 := by
    rw [← hzero]
    simpa [periodicSobolevSq] using
      (Summable.sum_le_tsum {k} (fun j _ => hnonneg j) hsumm)
  have hsq : ‖periodicFourierCoeff f k‖ ^ 2 = 0 := by
    have hw : 0 < periodicFrequencyWeight k ^ s :=
      Real.rpow_pos_of_pos
        (lt_of_lt_of_le zero_lt_one (one_le_periodicFrequencyWeight k)) s
    have hz : 0 ≤ ‖periodicFourierCoeff f k‖ ^ 2 := sq_nonneg _
    nlinarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)


/-- Spatial differentiation of a jointly smooth scalar field remains jointly
smooth when time is held fixed. -/
theorem spatialPartial_time_contDiff {F : SpaceTime → ℂ}
    (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : SpaceTime =>
      spatialPartial i (fun x => F (z.1, x)) z.2) := by
  have he : (fun z : SpaceTime => spatialPartial i (fun x => F (z.1, x)) z.2) =
      fun z => fderiv ℝ F z (0, coordinateVector i) := by
    funext z
    unfold spatialPartial
    have hd : HasFDerivAt (fun x : Space => F (z.1, x))
        ((fderiv ℝ F z).comp (ContinuousLinearMap.inr ℝ ℝ Space)) z.2 :=
      (hF.differentiable (by simp) (z.1, z.2)).hasFDerivAt.comp z.2
        (hasFDerivAt_prodMk_right z.1 z.2)
    rw [hd.fderiv]
    rfl
  rw [he]
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const

/-- Every integer-order periodic energy of a jointly smooth field is a
continuous function of time. The integral is over the fixed compact cube. -/
theorem continuous_periodicIntegerEnergy_time (n : ℕ) {F : SpaceTime → ℂ}
    (hF : ContDiff ℝ ∞ F) :
    Continuous (fun t => periodicIntegerEnergy n (fun x => F (t, x))) := by
  induction n generalizing F with
  | zero =>
      change Continuous (fun t => ∫ y in cube, ‖F (t, toSpace y)‖ ^ 2)
      apply continuous_parametric_integral_of_continuous _ isCompact_Icc
      exact (hF.continuous.comp
        (continuous_fst.prodMk (toSpace.continuous.comp continuous_snd))).norm.pow 2
  | succ n ih =>
      exact (ih hF).add (continuous_finsetSum _ (fun i _ =>
        ih (spatialPartial_time_contDiff hF i)))

end NSFormalization.Paper1
