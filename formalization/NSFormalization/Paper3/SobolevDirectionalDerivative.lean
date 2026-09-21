import NSFormalization.Paper3.SobolevOrderLowering
import NSFormalization.Paper3.SobolevDensity

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ENNReal SchwartzMap LineDeriv Real

/-- The bounded weighted directional derivative symbol. -/
def sobolevDirectionalSymbol (a ξ : Space) : ℂ :=
  (2 * π * Complex.I) * ((inner ℝ ξ a : ℂ) * sobolevBesselWeight (-1) ξ)

/-- The inverse-bracket bound used in Mathlib's Sobolev derivative proof. -/
theorem inner_besselInverse_norm_le (a ξ : Space) :
    ‖(inner ℝ ξ a : ℂ) * sobolevBesselWeight (-1) ξ‖ ≤ ‖a‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  simp only [sobolevBesselWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖ξ‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖ξ‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner ℝ ξ a| ^ 2 ≤ ‖a‖ ^ 2 * (1 + ‖ξ‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow, mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

theorem sobolevDirectionalSymbol_norm_le (a ξ : Space) :
    ‖sobolevDirectionalSymbol a ξ‖ ≤ (2 * π) * ‖a‖ := by
  have hc : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
    simp [Real.pi_pos.le]
  rw [sobolevDirectionalSymbol, norm_mul, hc]
  exact mul_le_mul_of_nonneg_left (inner_besselInverse_norm_le a ξ) (by positivity)

theorem sobolevDirectionalSymbol_memLp (a : Space) :
    MemLp (sobolevDirectionalSymbol a) ⊤ (volume : Measure Space) := by
  apply memLp_top_of_bound (C := (2 * π) * ‖a‖)
  · have hc : Continuous (sobolevDirectionalSymbol a) := by
      have hW := (sobolevBesselWeight_temperate (-1)).1.continuous
      unfold sobolevDirectionalSymbol
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (sobolevDirectionalSymbol_norm_le a)

/-- A bounded complex linear derivative on complete weighted Fourier data. -/
def sobolevDirectionalDerivative (s : ℝ) (a : Space) :
    SobolevHilbert s →L[ℂ] SobolevHilbert (s - 1) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure Space) ⊤ 2 2
    ((sobolevDirectionalSymbol_memLp a).toLp _)

theorem sobolevDirectionalDerivative_coeFn (s : ℝ) (a : Space) (h : SobolevHilbert s) :
    (sobolevDirectionalDerivative s a h : Space → ℂ) =ᵐ[volume]
      fun ξ => sobolevDirectionalSymbol a ξ * h ξ := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((sobolevDirectionalSymbol_memLp a).toLp _) h,
    (sobolevDirectionalSymbol_memLp a).coeFn_toLp] with ξ hξ gξ
  simpa [sobolevDirectionalDerivative, gξ] using hξ

theorem sobolevDirectionalDerivative_norm_le (s : ℝ) (a : Space) (h : SobolevHilbert s) :
    ‖sobolevDirectionalDerivative s a h‖ ≤ ((2 * π) * ‖a‖) * ‖h‖ := by
  have hg : ‖(sobolevDirectionalSymbol_memLp a).toLp _‖ ≤ (2 * π) * ‖a‖ := by
    rw [Lp.norm_toLp]
    have he := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure Space))
      (Filter.Eventually.of_forall (sobolevDirectionalSymbol_norm_le a))
    simpa only [eLpNorm_exponent_top, ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * π) * ‖a‖)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  change ‖(ContinuousLinearMap.mul ℂ ℂ).holder 2 _ h‖ ≤ _
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖(sobolevDirectionalSymbol_memLp a).toLp _‖ * ‖h‖ :=
      (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le _ _
    _ ≤ 1 * ((2 * π) * ‖a‖) * ‖h‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) hg (norm_nonneg _) (by norm_num))
      (norm_nonneg _)
    _ = _ := by ring

theorem sobolevDirectionalDerivative_opNorm_le (s : ℝ) (a : Space) :
    ‖sobolevDirectionalDerivative s a‖ ≤ (2 * π) * ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact sobolevDirectionalDerivative_norm_le s a

/-- The bounded data derivative agrees with the actual Schwartz derivative. -/
theorem sobolevDirectionalDerivative_weightedFourierLp (s : ℝ) (a : Space)
    (φ : SchwartzMap Space ℂ) :
    sobolevDirectionalDerivative s a (weightedFourierLp s φ) =
      weightedFourierLp (s - 1) (∂_{a} φ) := by
  apply Lp.ext
  filter_upwards [sobolevDirectionalDerivative_coeFn s a (weightedFourierLp s φ),
    weightedFourierLp_ae s φ, weightedFourierLp_ae (s - 1) (∂_{a} φ)] with ξ hD hφ hderivphi
  rw [hD, hφ, hderivphi, Complex.real_smul, Complex.real_smul]
  have hinner : (inner ℝ · a).HasTemperateGrowth := ((innerSL ℝ).flip a).hasTemperateGrowth
  have hF : 𝓕 (∂_{a} φ) ξ =
      (2 * π * Complex.I) * ((inner ℝ ξ a : ℂ) * 𝓕 φ ξ) := by
    have H := congrArg (fun ψ : SchwartzMap Space ℂ => ψ ξ)
      (SchwartzMap.fourier_lineDerivOp_eq φ a)
    simpa only [SchwartzMap.smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply hinner, smul_eq_mul, Complex.real_smul] using H
  change sobolevDirectionalSymbol a ξ * (sobolevBesselWeight s ξ * 𝓕 φ ξ) =
    sobolevBesselWeight (s - 1) ξ * 𝓕 (∂_{a} φ) ξ
  rw [hF]
  have hw : sobolevBesselWeight (-1) ξ * sobolevBesselWeight s ξ =
      sobolevBesselWeight (s - 1) ξ := by
    have H := congrFun (sobolevBesselWeight_mul (-1) s) ξ
    simpa only [Pi.mul_apply, show -1 + s = s - 1 by ring] using H
  unfold sobolevDirectionalSymbol
  calc
    _ = (2 * π * Complex.I) * (inner ℝ ξ a : ℂ) *
        (sobolevBesselWeight (-1) ξ * sobolevBesselWeight s ξ) * 𝓕 φ ξ := by ring
    _ = _ := by rw [hw]; ring

/-- On arbitrary complete data, the operator realizes the actual
 distributional directional derivative. -/
theorem sobolevRealization_directionalDerivative (s : ℝ) (a : Space) (h : SobolevHilbert s) :
    sobolevRealization (s - 1) (sobolevDirectionalDerivative s a h) =
      ∂_{a} (sobolevRealization s h) := by
  refine (denseRange_weightedFourierLp s).induction_on h
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro φ
  rw [sobolevDirectionalDerivative_weightedFourierLp,
    sobolevRealization_weightedFourierLp, sobolevRealization_weightedFourierLp]
  exact (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq φ a).symm

end NSFormalization.Paper3
