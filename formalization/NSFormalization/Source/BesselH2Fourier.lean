import NSFormalization.Paper3.WeightedFourierLp
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The quantitative dimension-three H2 Fourier L1 bound

The inverse Bessel weight is genuinely square integrable. Multiplication by
this weight maps arbitrary complex L2 representatives into L1, with a finite
integral-defined constant independent of support. The Schwartz specialization
uses the actual weighted Fourier representative, without a norm convention
identification or a local evolution premise.
-/
noncomputable section
open MeasureTheory Filter FourierTransform NavierStokes.ProblemStatement
open scoped ENNReal
namespace NSFormalization.Source.BesselH2Fourier

def besselInverse (ξ : Space) : ℝ := (1 + ‖ξ‖ ^ 2)⁻¹

theorem besselInverse_nonneg (ξ : Space) : 0 ≤ besselInverse ξ := by
  unfold besselInverse
  positivity

theorem integrable_besselInverse_sq :
    Integrable (fun ξ : Space => besselInverse ξ ^ 2) volume := by
  have h := integrable_rpow_neg_one_add_norm_sq
    (μ := (volume : Measure Space)) (r := 4) (by norm_num [Space])
  convert! h using 1
  ext ξ
  norm_num [besselInverse]

theorem besselInverse_memLp : MemLp besselInverse 2 (volume : Measure Space) := by
  apply (memLp_two_iff_integrable_sq _).mpr integrable_besselInverse_sq
  exact ((continuous_const.add (continuous_norm.pow 2)).inv₀
    (fun ξ : Space => ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2))).aestronglyMeasurable

/-- A finite real constant defined by the genuine integrable square. -/
def besselConstant : ℝ := (∫ ξ : Space, besselInverse ξ ^ 2) ^ (1 / (2 : ℝ))

theorem besselConstant_nonneg : 0 ≤ besselConstant := Real.rpow_nonneg (by positivity) _

theorem besselConstant_eq_eLpNorm :
    besselConstant = (eLpNorm besselInverse 2 (volume : Measure Space)).toReal := by
  rw [besselInverse_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, inv_eq_one_div]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [besselConstant, Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- Both integrability and the quantitative L2-to-L1 estimate hold for every
complex L2 representative, without pointwise regularity or support premises. -/
theorem product_integrable_bound {h : Space → ℂ} (hh : MemLp h 2 volume) :
    Integrable (fun ξ => (besselInverse ξ : ℂ) * h ξ) volume ∧
    (∫ ξ : Space, ‖(besselInverse ξ : ℂ) * h ξ‖) ≤
      besselConstant * (eLpNorm h 2 volume).toReal := by
  constructor
  · exact memLp_one_iff_integrable.mp (hh.mul' besselInverse_memLp.ofReal)
  · have hn : (∫ ξ : Space, ‖h ξ‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
        (eLpNorm h 2 volume).toReal := by
      rw [hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat, inv_eq_one_div]
      rw [ENNReal.toReal_ofReal (by positivity)]
    have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Eventually.of_forall besselInverse_nonneg)
      (Eventually.of_forall (fun ξ => norm_nonneg (h ξ)))
      (by simpa using besselInverse_memLp) (by simpa using hh.norm)
    rw [hn] at H
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (besselInverse_nonneg _), Real.rpow_two, besselConstant] using H

theorem lp_product_integrable_bound (h : Lp ℂ 2 (volume : Measure Space)) :
    Integrable (fun ξ => (besselInverse ξ : ℂ) * h ξ) volume ∧
    (∫ ξ : Space, ‖(besselInverse ξ : ℂ) * h ξ‖) ≤ besselConstant * ‖h‖ := by
  simpa only [Lp.norm_def] using product_integrable_bound (Lp.memLp h)

/-- Quantitative Fourier L1 control by the actual cycles-frequency weighted
H2 L2 vector for every Schwartz field. -/
theorem schwartz_fourier_integral_bound (φ : SchwartzMap Space ℂ) :
    (∫ ξ : Space, ‖𝓕 (φ : Space → ℂ) ξ‖) ≤
      besselConstant * ‖NSFormalization.Paper3.weightedFourierLp 2 φ‖ := by
  have H := (lp_product_integrable_bound
    (NSFormalization.Paper3.weightedFourierLp 2 φ)).2
  have he : (fun ξ => (besselInverse ξ : ℂ) *
      NSFormalization.Paper3.weightedFourierLp 2 φ ξ) =ᵐ[volume]
      𝓕 (φ : Space → ℂ) := by
    filter_upwards [NSFormalization.Paper3.weightedFourierLp_ae 2 φ] with ξ hξ
    rw [hξ]
    norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    simp [besselInverse, ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2)]
  have hi : (∫ ξ : Space, ‖(besselInverse ξ : ℂ) *
      NSFormalization.Paper3.weightedFourierLp 2 φ ξ‖) =
      ∫ ξ : Space, ‖𝓕 (φ : Space → ℂ) ξ‖ := by
    exact integral_congr_ae (he.fun_comp norm)
  exact hi ▸ H

/-- The cycles-frequency H2 norm controls every point of the actual Schwartz
field, with a constant independent of support. -/
theorem schwartz_pointwise_bound (φ : SchwartzMap Space ℂ) (x : Space) :
    ‖φ x‖ ≤ besselConstant * ‖NSFormalization.Paper3.weightedFourierLp 2 φ‖ := by
  have hinv : 𝓕⁻ (𝓕 (φ : Space → ℂ)) x = φ x := by
    have H := congrArg (fun ψ : SchwartzMap Space ℂ => ψ x)
      (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap Space ℂ) φ)
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using H
  calc
    ‖φ x‖ = ‖𝓕⁻ (𝓕 (φ : Space → ℂ)) x‖ := congrArg norm hinv.symm
    _ ≤ ∫ ξ : Space, ‖𝓕 (φ : Space → ℂ) ξ‖ := by
      rw [Real.fourierInv_eq]
      exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Circle.norm_smul])
    _ ≤ _ := schwartz_fourier_integral_bound φ

end NSFormalization.Source.BesselH2Fourier
