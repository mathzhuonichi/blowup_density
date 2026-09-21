import NSFormalization.Paper3.CompactSobolevRealization

/-! # Contractive lowering of complete Sobolev data

The existing Mathlib Hölder continuous bilinear map multiplies weighted Fourier
L² data by the bounded inverse Bessel symbol. No finite-volume premise is used.
-/
noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ENNReal SchwartzMap

theorem sobolevBesselWeight_norm_le_one {t : ℝ} (ht : t ≤ 0) (ξ : Space) :
    ‖sobolevBesselWeight t ξ‖ ≤ 1 := by
  simp only [sobolevBesselWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)

/-- The inverse Bessel symbol is an L∞ multiplier. -/
theorem sobolevOrderLoweringSymbolMemLp (s r : ℝ) (hrs : r ≤ s) :
    MemLp (sobolevBesselWeight (r - s)) ⊤ (volume : Measure Space) :=
  memLp_top_of_bound (sobolevBesselWeight_temperate (r-s)).1.continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (sobolevBesselWeight_norm_le_one (sub_nonpos.mpr hrs)))

/-- Contractive change of weighted Fourier data from order `s` to order `r`. -/
def sobolevOrderLowering (s r : ℝ) (hrs : r ≤ s) :
    SobolevHilbert s →L[ℂ] SobolevHilbert r :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure Space) ⊤ 2 2
    ((sobolevOrderLoweringSymbolMemLp s r hrs).toLp _)

theorem sobolevOrderLowering_coeFn (s r : ℝ) (hrs : r ≤ s) (h : SobolevHilbert s) :
    (sobolevOrderLowering s r hrs h : Space → ℂ) =ᵐ[volume]
      fun ξ => sobolevBesselWeight (r - s) ξ * h ξ := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((sobolevOrderLoweringSymbolMemLp s r hrs).toLp _) h,
    (sobolevOrderLoweringSymbolMemLp s r hrs).coeFn_toLp] with ξ hξ gξ
  simpa [sobolevOrderLowering, gξ] using hξ

theorem sobolevOrderLowering_norm_le (s r : ℝ) (hrs : r ≤ s) (h : SobolevHilbert s) :
    ‖sobolevOrderLowering s r hrs h‖ ≤ ‖h‖ := by
  have hg : ‖(sobolevOrderLoweringSymbolMemLp s r hrs).toLp _‖ ≤ 1 := by
    rw [Lp.norm_toLp]
    have he := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure Space))
      (Filter.Eventually.of_forall (sobolevBesselWeight_norm_le_one (sub_nonpos.mpr hrs)))
    simpa only [eLpNorm_exponent_top, ENNReal.ofReal_one, ENNReal.toReal_one] using
      ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) (by simpa using he)
  change ‖(ContinuousLinearMap.mul ℂ ℂ).holder 2 _ h‖ ≤ _
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖(sobolevOrderLoweringSymbolMemLp s r hrs).toLp _‖ * ‖h‖ :=
      (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le _ _
    _ ≤ 1 * 1 * ‖h‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) hg (norm_nonneg _) (by norm_num))
      (norm_nonneg _)
    _ = _ := by ring

theorem sobolevOrderLowering_opNorm_le (s r : ℝ) (hrs : r ≤ s) :
    ‖sobolevOrderLowering s r hrs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  simpa using sobolevOrderLowering_norm_le s r hrs h

theorem sobolevOrderLowering_toDistribution (s r : ℝ) (hrs : r ≤ s)
    (h : SobolevHilbert s) :
    (sobolevOrderLowering s r hrs h : 𝓢'(Space, ℂ)) =
      sobolevWeightMultiplier (r - s) (h : 𝓢'(Space, ℂ)) := by
  have he : sobolevOrderLowering s r hrs h =
      ((sobolevOrderLoweringSymbolMemLp s r hrs).toLp _ • h : Lp ℂ 2 volume) := by
    apply Lp.ext
    filter_upwards [sobolevOrderLowering_coeFn s r hrs h,
      Lp.coeFn_lpSMul (r := 2) ((sobolevOrderLoweringSymbolMemLp s r hrs).toLp _) h,
      (sobolevOrderLoweringSymbolMemLp s r hrs).coeFn_toLp] with ξ hξ kξ gξ
    simp [hξ, kξ, gξ]
  rw [he]
  exact Lp.toTemperedDistribution_smul_eq (sobolevBesselWeight_temperate (r-s))
    (sobolevOrderLoweringSymbolMemLp s r hrs) h

/-- Lowering preserves the actual physical tempered distribution. -/
theorem sobolevRealization_orderLowering (s r : ℝ) (hrs : r ≤ s) (h : SobolevHilbert s) :
    sobolevRealization r (sobolevOrderLowering s r hrs h) = sobolevRealization s h := by
  simp only [sobolevRealization_apply, sobolevOrderLowering_toDistribution]
  change 𝓕⁻ (sobolevWeightMultiplier (-r) (sobolevWeightMultiplier (r-s) _)) =
    𝓕⁻ (sobolevWeightMultiplier (-s) _)
  rw [sobolevWeightMultiplier_add, show r-s + -r = -s by ring]

theorem sobolevOrderLowering_weightedFourierLp (s r : ℝ) (hrs : r ≤ s)
    (φ : SchwartzMap Space ℂ) :
    sobolevOrderLowering s r hrs (weightedFourierLp s φ) = weightedFourierLp r φ := by
  apply sobolevRealization_injective r
  rw [sobolevRealization_orderLowering, sobolevRealization_weightedFourierLp,
    sobolevRealization_weightedFourierLp]

end NSFormalization.Paper3
