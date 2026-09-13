import Mathlib.Analysis.Normed.Operator.Mul
import Formal.R3L2ScalarAux
import Formal.R3YoungL1L2Bochner

namespace MNS2

open MeasureTheory

noncomputable section

/-- Fiberwise scalar multiplication, with the vector argument first: `(v, c) ↦ c • v`. -/
def r3ScalarVelocityFiberBilinear :
    R3C →L[ℂ] ℂ →L[ℂ] R3C :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] R3C →L[ℂ] R3C).flip

@[simp]
theorem r3ScalarVelocityFiberBilinear_apply (v : R3C) (c : ℂ) :
    r3ScalarVelocityFiberBilinear v c = c • v := by
  rfl

/-- The operator norm of `c ↦ c • v` is exactly `‖v‖`. -/
theorem norm_r3ScalarVelocityFiberBilinear_apply (v : R3C) :
    ‖r3ScalarVelocityFiberBilinear v‖ = ‖v‖ := by
  change
    ‖(ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] R3C →L[ℂ] R3C).flip v‖ = ‖v‖
  rw [ContinuousLinearMap.lsmul_flip_apply]
  simpa using (ContinuousLinearMap.toSpanSingletonLIE ℂ R3C).norm_map v

/--
Pointwise scalar multiplication lifted from scalar `L²(R³)` to velocity `L²(R³)` as a continuous
bilinear map.
-/
def r3L2ScalarSmulVelocity :
    R3C →L[ℂ] R3L2ScalarAux →L[ℂ] R3L2Velocity :=
  r3ScalarVelocityFiberBilinear.compLpL₂ 2 (volume : Measure R3)

@[simp]
theorem r3L2ScalarSmulVelocity_apply (v : R3C) (a : R3L2ScalarAux) :
    r3L2ScalarSmulVelocity v a =
      (r3ScalarVelocityFiberBilinear v).compLp a := by
  rfl

/-- Fiberwise multiplication by `v` sends scalar `L²` to velocity `L²` with the expected bound. -/
theorem norm_r3L2ScalarSmulVelocity_le (v : R3C) (a : R3L2ScalarAux) :
    ‖r3L2ScalarSmulVelocity v a‖ ≤ ‖v‖ * ‖a‖ := by
  rw [r3L2ScalarSmulVelocity_apply]
  calc
    ‖(r3ScalarVelocityFiberBilinear v).compLp a‖ ≤
        ‖r3ScalarVelocityFiberBilinear v‖ * ‖a‖ :=
      ContinuousLinearMap.norm_compLp_le _ _
    _ = ‖v‖ * ‖a‖ := by
      rw [norm_r3ScalarVelocityFiberBilinear_apply]

/-- Translation of a scalar `L²(R³)` field by `y`, using the same measure-preserving translation
as the velocity-valued Young bridge. -/
def r3L2ScalarTranslate (y : R3) (a : R3L2ScalarAux) : R3L2ScalarAux :=
  Lp.compMeasurePreserving (r3TranslationMap y)
    (measurePreserving_r3TranslationMap y) a

@[simp]
theorem norm_r3L2ScalarTranslate (y : R3) (a : R3L2ScalarAux) :
    ‖r3L2ScalarTranslate y a‖ = ‖a‖ := by
  exact Lp.norm_compMeasurePreserving a (measurePreserving_r3TranslationMap y)

/-- The scalar `L²` translation orbit is continuous in the translation parameter. -/
theorem continuous_r3L2ScalarTranslate (a : R3L2ScalarAux) :
    Continuous (fun y : R3 => r3L2ScalarTranslate y a) := by
  unfold r3L2ScalarTranslate
  have ha : Continuous (fun _ : R3 => a) := continuous_const
  exact ha.compMeasurePreservingLp continuous_r3TranslationMap
    (fun y => measurePreserving_r3TranslationMap y) (by simp)

/--
The right-oriented Young integrand `a(x-y) b(y)`, represented as an `L²` velocity field without
choosing a pointwise representative of the scalar `L²` input.
-/
def r3YoungL2L1Integrand
    (a : R3L2ScalarAux) (b : R3SchwartzVelocity) (y : R3) : R3L2Velocity :=
  r3L2ScalarSmulVelocity (b y) (r3L2ScalarTranslate y a)

/-- Pointwise norm majorization for the right-oriented Young integrand. -/
theorem norm_r3YoungL2L1Integrand_le
    (a : R3L2ScalarAux) (b : R3SchwartzVelocity) (y : R3) :
    ‖r3YoungL2L1Integrand a b y‖ ≤ ‖b y‖ * ‖a‖ := by
  unfold r3YoungL2L1Integrand
  calc
    ‖r3L2ScalarSmulVelocity (b y) (r3L2ScalarTranslate y a)‖ ≤
        ‖b y‖ * ‖r3L2ScalarTranslate y a‖ :=
      norm_r3L2ScalarSmulVelocity_le (b y) (r3L2ScalarTranslate y a)
    _ = ‖b y‖ * ‖a‖ := by
      rw [norm_r3L2ScalarTranslate]

/-- The right-oriented Young integrand is continuous. -/
theorem continuous_r3YoungL2L1Integrand
    (a : R3L2ScalarAux) (b : R3SchwartzVelocity) :
    Continuous (fun y : R3 => r3YoungL2L1Integrand a b y) := by
  unfold r3YoungL2L1Integrand
  have hb : Continuous (fun y : R3 => b y) := b.continuous
  have ha : Continuous (fun y : R3 => r3L2ScalarTranslate y a) :=
    continuous_r3L2ScalarTranslate a
  exact (r3L2ScalarSmulVelocity.continuous.comp hb).clm_apply ha

/-- The right-oriented Young integrand is Bochner integrable for a Schwartz velocity factor. -/
theorem integrable_r3YoungL2L1Integrand
    (a : R3L2ScalarAux) (b : R3SchwartzVelocity) :
    Integrable (fun y : R3 => r3YoungL2L1Integrand a b y) := by
  have hmajor : Integrable (fun y : R3 => ‖b y‖ * ‖a‖) :=
    (Integrable.norm b.integrable).mul_const ‖a‖
  exact hmajor.mono'
    (continuous_r3YoungL2L1Integrand a b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => norm_r3YoungL2L1Integrand_le a b y)

/-- The right-oriented `L² * L¹` Bochner convolution. -/
def r3YoungL2L1Convolution
    (a : R3L2ScalarAux) (b : R3SchwartzVelocity) : R3L2Velocity :=
  ∫ y : R3, r3YoungL2L1Integrand a b y

/-- Young's `L² * L¹ → L²` estimate in the scalar-vector orientation needed by the additive H²
convolution split. -/
theorem norm_r3YoungL2L1Convolution_le
    (a : R3L2ScalarAux) (b : R3SchwartzVelocity) :
    ‖r3YoungL2L1Convolution a b‖ ≤ ‖a‖ * (∫ y : R3, ‖b y‖) := by
  have hint : Integrable (fun y : R3 => ‖r3YoungL2L1Integrand a b y‖) :=
    (integrable_r3YoungL2L1Integrand a b).norm
  have hmajor : Integrable (fun y : R3 => ‖b y‖ * ‖a‖) :=
    (Integrable.norm b.integrable).mul_const ‖a‖
  calc
    ‖r3YoungL2L1Convolution a b‖ =
        ‖∫ y : R3, r3YoungL2L1Integrand a b y‖ := by
      rfl
    _ ≤ ∫ y : R3, ‖r3YoungL2L1Integrand a b y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : R3, ‖b y‖ * ‖a‖ :=
      integral_mono hint hmajor (fun y => norm_r3YoungL2L1Integrand_le a b y)
    _ = (∫ y : R3, ‖b y‖) * ‖a‖ := by
      rw [integral_mul_const]
    _ = ‖a‖ * (∫ y : R3, ‖b y‖) := by
      rw [mul_comm]

end

end MNS2
