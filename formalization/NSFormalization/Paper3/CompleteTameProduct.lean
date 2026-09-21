import NSFormalization.Source.FourierTameProduct
import NSFormalization.Paper3.SobolevOrderLowering
import NSFormalization.Paper3.SobolevDensity
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source.FourierTameProduct

/-- The support-independent constant already proved on Schwartz data. -/
def sobolevTameConstant (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (m - 1) * NSFormalization.Source.BesselH2Fourier.besselConstant

theorem sobolevTameConstant_nonneg (m : ℕ) : 0 ≤ sobolevTameConstant m :=
  mul_nonneg (by positivity) NSFormalization.Source.BesselH2Fourier.besselConstant_nonneg

private theorem low_norm_le (m : ℕ) (hm : 2 ≤ m) (φ : SchwartzMap Space ℂ) :
    ‖weightedFourierLp 2 φ‖ ≤ ‖weightedFourierLp m φ‖ := by
  have hr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  simpa only [sobolevOrderLowering_weightedFourierLp] using
    sobolevOrderLowering_norm_le m 2 hr (weightedFourierLp m φ)

private def productRightLinear (m : ℕ) (φ : SchwartzMap Space ℂ) :
    SchwartzMap Space ℂ →ₗ[ℝ] SobolevHilbert m :=
  (weightedFourierLp m).toLinearMap.comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ) φ).toLinearMap

private theorem productRightLinear_apply (m : ℕ) (φ ψ : SchwartzMap Space ℂ) :
    productRightLinear m φ ψ = weightedFourierLp m (schwartzProduct φ ψ) := by
  change weightedFourierLp m (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ) φ ψ) = _
  apply congrArg (weightedFourierLp m)
  ext x
  rfl

private theorem product_coarse_bound (m : ℕ) (hm : 2 ≤ m) (φ ψ : SchwartzMap Space ℂ) :
    ‖productRightLinear m φ ψ‖ ≤
      (2 * sobolevTameConstant m * ‖weightedFourierLp m φ‖) * ‖weightedFourierLp m ψ‖ := by
  rw [productRightLinear_apply]
  calc
    _ ≤ sobolevTameConstant m *
        (‖weightedFourierLp 2 ψ‖ * ‖weightedFourierLp m φ‖ +
          ‖weightedFourierLp 2 φ‖ * ‖weightedFourierLp m ψ‖) := schwartz_tame_product m φ ψ
    _ ≤ sobolevTameConstant m *
        (‖weightedFourierLp m ψ‖ * ‖weightedFourierLp m φ‖ +
          ‖weightedFourierLp m φ‖ * ‖weightedFourierLp m ψ‖) := by
      gcongr
      · exact sobolevTameConstant_nonneg m
      · exact low_norm_le m hm ψ
      · exact low_norm_le m hm φ
    _ = _ := by ring

/-- First extension: multiplication by a fixed Schwartz left factor. -/
def sobolevProductRight (m : ℕ) (φ : SchwartzMap Space ℂ) :
    SobolevHilbert m →L[ℝ] SobolevHilbert m :=
  (productRightLinear m φ).extendOfNorm (weightedFourierLp m).toLinearMap

theorem sobolevProductRight_weightedFourierLp (m : ℕ) (hm : 2 ≤ m)
    (φ ψ : SchwartzMap Space ℂ) :
    sobolevProductRight m φ (weightedFourierLp m ψ) =
      weightedFourierLp m (schwartzProduct φ ψ) := by
  exact (LinearMap.extendOfNorm_eq (f := productRightLinear m φ)
    (e := (weightedFourierLp m).toLinearMap) (denseRange_weightedFourierLp m)
    ⟨_, product_coarse_bound m hm φ⟩ ψ).trans (productRightLinear_apply m φ ψ)

theorem sobolevProductRight_norm_le (m : ℕ) (hm : 2 ≤ m) (φ : SchwartzMap Space ℂ) :
    ‖sobolevProductRight m φ‖ ≤ 2 * sobolevTameConstant m * ‖weightedFourierLp m φ‖ := by
  apply LinearMap.opNorm_extendOfNorm_le (denseRange_weightedFourierLp m)
  · exact mul_nonneg (mul_nonneg (by norm_num) (sobolevTameConstant_nonneg m)) (norm_nonneg _)
  · exact product_coarse_bound m hm φ

/-- The first extension depends linearly on the Schwartz left factor. -/
def sobolevProductLeftLinear (m : ℕ) (hm : 2 ≤ m) :
    SchwartzMap Space ℂ →ₗ[ℝ] (SobolevHilbert m →L[ℝ] SobolevHilbert m) where
  toFun := sobolevProductRight m
  map_add' φ ψ := by
    apply ContinuousLinearMap.ext
    intro h
    refine (denseRange_weightedFourierLp m).induction_on h
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro χ
    simp only [_root_.add_apply, sobolevProductRight_weightedFourierLp m hm]
    rw [← map_add]
    apply congrArg (weightedFourierLp m)
    ext x
    simp [schwartzProduct_apply, add_mul]
  map_smul' c φ := by
    apply ContinuousLinearMap.ext
    intro h
    refine (denseRange_weightedFourierLp m).induction_on h
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro χ
    simp only [_root_.smul_apply, sobolevProductRight_weightedFourierLp m hm,
      RingHom.id_apply]
    rw [← map_smul]
    apply congrArg (weightedFourierLp m)
    ext x
    simp [schwartzProduct_apply, mul_assoc]

/-- Actual continuous bilinear multiplication on complete Sobolev data. -/
def sobolevProduct (m : ℕ) (hm : 2 ≤ m) :
    SobolevHilbert m →L[ℝ] SobolevHilbert m →L[ℝ] SobolevHilbert m :=
  (sobolevProductLeftLinear m hm).extendOfNorm (weightedFourierLp m).toLinearMap

theorem sobolevProduct_weightedFourierLp_left (m : ℕ) (hm : 2 ≤ m)
    (φ : SchwartzMap Space ℂ) :
    sobolevProduct m hm (weightedFourierLp m φ) = sobolevProductRight m φ := by
  exact LinearMap.extendOfNorm_eq (f := sobolevProductLeftLinear m hm)
    (e := (weightedFourierLp m).toLinearMap) (denseRange_weightedFourierLp m)
    ⟨2 * sobolevTameConstant m, sobolevProductRight_norm_le m hm⟩ φ

/-- Compatibility with the actual pointwise Schwartz product. -/
theorem sobolevProduct_weightedFourierLp (m : ℕ) (hm : 2 ≤ m)
    (φ ψ : SchwartzMap Space ℂ) :
    sobolevProduct m hm (weightedFourierLp m φ) (weightedFourierLp m ψ) =
      weightedFourierLp m (schwartzProduct φ ψ) := by
  rw [sobolevProduct_weightedFourierLp_left, sobolevProductRight_weightedFourierLp m hm]

/-- The coarse bound is used to construct the continuous bilinear map. -/
theorem sobolevProduct_opNorm_le (m : ℕ) (hm : 2 ≤ m) :
    ‖sobolevProduct m hm‖ ≤ 2 * sobolevTameConstant m := by
  apply LinearMap.opNorm_extendOfNorm_le (denseRange_weightedFourierLp m)
  · exact mul_nonneg (by norm_num) (sobolevTameConstant_nonneg m)
  · exact sobolevProductRight_norm_le m hm

/-- The exact H2/Hm tame inequality on all complete data. Dense transport
retains both lowered H2 norms; no approximation premise is required. -/
theorem sobolevProduct_tame_bound (m : ℕ) (hm : 2 ≤ m)
    (h k : SobolevHilbert m) :
    ‖sobolevProduct m hm h k‖ ≤ sobolevTameConstant m *
      (‖sobolevOrderLowering m 2 (by exact_mod_cast hm) k‖ * ‖h‖ +
        ‖sobolevOrderLowering m 2 (by exact_mod_cast hm) h‖ * ‖k‖) := by
  refine (denseRange_weightedFourierLp m).induction_on h
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro φ
  refine (denseRange_weightedFourierLp m).induction_on k
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro ψ
  rw [sobolevProduct_weightedFourierLp,
    sobolevOrderLowering_weightedFourierLp, sobolevOrderLowering_weightedFourierLp]
  exact schwartz_tame_product m φ ψ

end NSFormalization.Paper3
