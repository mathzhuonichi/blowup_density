import NSFormalization.Paper3.SobolevOrderLowering
import NSFormalization.Paper3.SobolevDensity
import NSFormalization.Source.BesselH2Fourier
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Bounded continuous physical representatives of complete Sobolev data -/
noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ENNReal SchwartzMap
open NSFormalization.Source.BesselH2Fourier

private theorem schwartz_bounded_norm (φ : SchwartzMap Space ℂ) :
    ‖SchwartzMap.toBoundedContinuousFunctionCLM ℝ Space ℂ φ‖ ≤
      besselConstant * ‖weightedFourierLp 2 φ‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg besselConstant_nonneg (norm_nonneg _))).mpr
  exact schwartz_pointwise_bound φ

/-- The complete H2 datum's bounded continuous physical representative. -/
def sobolevBoundedRepresentative2 : SobolevHilbert 2 →L[ℝ] (BoundedContinuousFunction Space ℂ) :=
  (SchwartzMap.toBoundedContinuousFunctionCLM ℝ Space ℂ).toLinearMap.extendOfNorm
    (weightedFourierLp 2).toLinearMap

theorem sobolevBoundedRepresentative2_norm_le (h : SobolevHilbert 2) :
    ‖sobolevBoundedRepresentative2 h‖ ≤ besselConstant * ‖h‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_weightedFourierLp 2) _ schwartz_bounded_norm h

@[simp] theorem sobolevBoundedRepresentative2_weightedFourierLp (φ : SchwartzMap Space ℂ) :
    sobolevBoundedRepresentative2 (weightedFourierLp 2 φ) =
      SchwartzMap.toBoundedContinuousFunctionCLM ℝ Space ℂ φ :=
  LinearMap.extendOfNorm_eq (denseRange_weightedFourierLp 2) ⟨_, schwartz_bounded_norm⟩ φ

/-- The bounded continuous representative at every real order at least two. -/
def sobolevBoundedRepresentative (m : ℝ) (hm : 2 ≤ m) :
    SobolevHilbert m →L[ℝ] (BoundedContinuousFunction Space ℂ) :=
  sobolevBoundedRepresentative2.comp ((sobolevOrderLowering m 2 hm).restrictScalars ℝ)

theorem sobolevBoundedRepresentative_norm_le (m : ℝ) (hm : 2 ≤ m) (h : SobolevHilbert m) :
    ‖sobolevBoundedRepresentative m hm h‖ ≤
      besselConstant * ‖sobolevOrderLowering m 2 hm h‖ :=
  sobolevBoundedRepresentative2_norm_le _

@[simp] theorem sobolevBoundedRepresentative_weightedFourierLp (m : ℝ) (hm : 2 ≤ m)
    (φ : SchwartzMap Space ℂ) :
    sobolevBoundedRepresentative m hm (weightedFourierLp m φ) =
      SchwartzMap.toBoundedContinuousFunctionCLM ℝ Space ℂ φ := by
  change sobolevBoundedRepresentative2 (sobolevOrderLowering m 2 hm _) = _
  rw [sobolevOrderLowering_weightedFourierLp, sobolevBoundedRepresentative2_weightedFourierLp]

theorem schwartz_mul_bounded_integrable (θ : SchwartzMap Space ℂ) (v : BoundedContinuousFunction Space ℂ) :
    Integrable (fun x => θ x * v x) := by
  exact (ContinuousLinearMap.mul ℂ ℂ).integrable_of_bilin_of_bdd_right ‖v‖ θ.integrable
    v.continuous.aestronglyMeasurable (Filter.Eventually.of_forall v.norm_coe_le_norm)

private def boundedTestLinear (θ : SchwartzMap Space ℂ) : (BoundedContinuousFunction Space ℂ) →ₗ[ℝ] ℂ where
  toFun v := ∫ x : Space, θ x * v x
  map_add' v w := by
    simp only [BoundedContinuousFunction.add_apply, mul_add]
    exact integral_add (schwartz_mul_bounded_integrable θ v) (schwartz_mul_bounded_integrable θ w)
  map_smul' c v := by
    simp only [BoundedContinuousFunction.smul_apply, RingHom.id_apply, mul_smul_comm]
    exact integral_smul c _

/-- Integration against a Schwartz test on bounded continuous fields. -/
def boundedSchwartzTest (θ : SchwartzMap Space ℂ) : (BoundedContinuousFunction Space ℂ) →L[ℝ] ℂ :=
  (boundedTestLinear θ).mkContinuous (∫ x : Space, ‖θ x‖) (by
    intro v
    change ‖∫ x : Space, θ x * v x‖ ≤ _
    calc
      _ ≤ ∫ x : Space, ‖θ x * v x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : Space, ‖θ x‖ * ‖v‖ := by
        apply integral_mono (schwartz_mul_bounded_integrable θ v).norm
          (θ.integrable.norm.mul_const _)
        intro x
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (v.norm_coe_le_norm x) (norm_nonneg _)
      _ = _ := integral_mul_const _ _)

@[simp] theorem boundedSchwartzTest_apply (θ : SchwartzMap Space ℂ) (v : BoundedContinuousFunction Space ℂ) :
    boundedSchwartzTest θ v = ∫ x : Space, θ x * v x := rfl

/-- The extended bounded representative realizes precisely the original distribution. -/
theorem sobolevRealization_boundedRepresentative2 (h : SobolevHilbert 2)
    (θ : SchwartzMap Space ℂ) :
    sobolevRealization 2 h θ = ∫ x : Space, θ x * sobolevBoundedRepresentative2 h x := by
  have hc : Continuous (fun h : SobolevHilbert 2 => sobolevRealization 2 h θ) := by fun_prop
  have hd : Continuous (fun h : SobolevHilbert 2 => boundedSchwartzTest θ (sobolevBoundedRepresentative2 h)) := by fun_prop
  change sobolevRealization 2 h θ = boundedSchwartzTest θ (sobolevBoundedRepresentative2 h)
  exact (denseRange_weightedFourierLp 2).induction (fun x hx => by
    obtain ⟨φ, rfl⟩ := hx
    simp only [sobolevRealization_weightedFourierLp, sobolevBoundedRepresentative2_weightedFourierLp,
      boundedSchwartzTest_apply, SchwartzMap.coe_apply]
    rfl) (isClosed_eq hc hd) h

theorem sobolevRealization_boundedRepresentative (m : ℝ) (hm : 2 ≤ m)
    (h : SobolevHilbert m) (θ : SchwartzMap Space ℂ) :
    sobolevRealization m h θ = ∫ x : Space, θ x * sobolevBoundedRepresentative m hm h x := by
  rw [← sobolevRealization_orderLowering m 2 hm h]
  exact sobolevRealization_boundedRepresentative2 _ θ

end NSFormalization.Paper3
