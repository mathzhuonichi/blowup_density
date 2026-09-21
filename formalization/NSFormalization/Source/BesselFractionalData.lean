import NSFormalization.Paper3.SobolevOrderLowering
import NSFormalization.Source.RieszSingularMultiplier

/-! # Fractional data from the complete inhomogeneous Sobolev model -/
noncomputable section
namespace NSFormalization.Source.BesselFractionalData
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open scoped ENNReal SchwartzMap

/-- The bounded fractional derivative of the inverse Bessel weight. -/
def symbol (a : ℝ) (ξ : Space) : ℂ :=
  (‖ξ‖ ^ a : ℝ) * sobolevBesselWeight (-a) ξ

theorem symbol_norm_le_one (a : ℝ) (ha : 0 ≤ a) (ξ : Space) :
    ‖symbol a ξ‖ ≤ 1 := by
  have hb : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hp : ‖ξ‖ ^ a ≤ (1 + ‖ξ‖ ^ 2) ^ (a / 2) := by
    calc
      ‖ξ‖ ^ a = (‖ξ‖ ^ (2 : ℝ)) ^ (a / 2) := by
        rw [← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ (a / 2) :=
        Real.rpow_le_rpow (by positivity) (by simp) (by positivity)
  simp only [symbol, norm_mul, sobolevBesselWeight, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg ξ) a),
    abs_of_nonneg (Real.rpow_nonneg hb.le (-a / 2))]
  calc
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ (a / 2) * (1 + ‖ξ‖ ^ 2) ^ (-a / 2) :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hb.le _)
    _ = 1 := by rw [← Real.rpow_add hb, show a / 2 + -a / 2 = 0 by ring, Real.rpow_zero]

theorem symbol_measurable (a : ℝ) : Measurable (symbol a) := by
  unfold symbol
  exact (Complex.measurable_ofReal.comp (measurable_norm.pow_const a)).mul
    (sobolevBesselWeight_temperate (-a)).1.continuous.measurable

theorem symbol_memLp (a : ℝ) (ha : 0 ≤ a) :
    MemLp (symbol a) ⊤ (volume : Measure Space) :=
  memLp_top_of_bound (symbol_measurable a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (symbol_norm_le_one a ha))

/-- Contractive fractional Fourier datum for every element of the completion. -/
def datum (a : ℝ) (ha : 0 ≤ a) : SobolevHilbert a →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure Space) ⊤ 2 2
    ((symbol_memLp a ha).toLp _)

theorem datum_coeFn (a : ℝ) (ha : 0 ≤ a) (h : SobolevHilbert a) :
    (datum a ha h : Space → ℂ) =ᵐ[volume] fun ξ => symbol a ξ * h ξ := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((symbol_memLp a ha).toLp _) h, (symbol_memLp a ha).coeFn_toLp] with ξ hξ gξ
  simpa [datum, gξ] using hξ

theorem datum_norm_le (a : ℝ) (ha : 0 ≤ a) (h : SobolevHilbert a) :
    ‖datum a ha h‖ ≤ ‖h‖ := by
  have hg : ‖(symbol_memLp a ha).toLp _‖ ≤ 1 := by
    rw [Lp.norm_toLp]
    have he := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure Space))
      (Filter.Eventually.of_forall (symbol_norm_le_one a ha))
    simpa only [eLpNorm_exponent_top, ENNReal.ofReal_one, ENNReal.toReal_one] using
      ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) (by simpa using he)
  change ‖(ContinuousLinearMap.mul ℂ ℂ).holder 2 _ h‖ ≤ _
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖(symbol_memLp a ha).toLp _‖ * ‖h‖ :=
      (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le _ _
    _ ≤ 1 * 1 * ‖h‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) hg (norm_nonneg _) (by norm_num))
      (norm_nonneg _)
    _ = _ := by ring

theorem datum_opNorm_le (a : ℝ) (ha : 0 ≤ a) : ‖datum a ha‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  simpa using datum_norm_le a ha h

theorem symbol_cancel (a : ℝ) {ξ : Space} (hξ : ξ ≠ 0) :
    NSFormalization.RieszFrequencyCutoffs.symbol a ξ * symbol a ξ =
      sobolevBesselWeight (-a) ξ := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  unfold NSFormalization.RieszFrequencyCutoffs.symbol symbol
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hn]
  simp

/-- Exact singular cancellation for arbitrary complete Sobolev data. -/
theorem multiplier_datum (a : ℝ) (ha : 0 ≤ a) (ha3 : a < 3/2)
    (h : SobolevHilbert a) :
    NSFormalization.RieszSingularMultiplier.multiplier a ha ha3 (datum a ha h) =
      𝓕 (sobolevRealization a h) := by
  have hr : 𝓕 (sobolevRealization a h) =
      sobolevWeightMultiplier (-a) (h : 𝓢'(Space, ℂ)) := by
    change 𝓕 (𝓕⁻ (sobolevWeightMultiplier (-a) (h : 𝓢'(Space, ℂ)))) = _
    exact fourier_fourierInv_eq _
  rw [hr, show sobolevWeightMultiplier (-a) (h : 𝓢'(Space, ℂ)) =
      (sobolevOrderLowering a 0 ha h : 𝓢'(Space, ℂ)) from
      (by simpa using (sobolevOrderLowering_toDistribution a 0 ha h).symm)]
  ext φ
  rw [NSFormalization.RieszSingularMultiplier.multiplier_pairing,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [datum_coeFn a ha h, sobolevOrderLowering_coeFn a 0 ha h,
    volume.ae_ne (0 : Space)] with ξ hd hl hξ
  simp only [hd, hl, zero_sub, smul_eq_mul]
  rw [← mul_assoc (NSFormalization.RieszFrequencyCutoffs.symbol a ξ), symbol_cancel a hξ]

end NSFormalization.Source.BesselFractionalData
