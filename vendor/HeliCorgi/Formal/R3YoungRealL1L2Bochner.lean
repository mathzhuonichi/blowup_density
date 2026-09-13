import Formal.R3YoungL1L2Bochner

namespace MNS2

open MeasureTheory

noncomputable section

/-- Real-valued `L²(R³)` used for nonnegative scalar convolution majorants. -/
abbrev R3L2RealScalar := Lp (α := R3) ℝ 2 (volume : Measure R3)

/-- Translation of a real `L²(R³)` field by `y`, using the physical map `x ↦ x-y`. -/
def r3L2RealTranslate (y : R3) (g : R3L2RealScalar) : R3L2RealScalar :=
  Lp.compMeasurePreserving (r3TranslationMap y)
    (measurePreserving_r3TranslationMap y) g

@[simp]
theorem norm_r3L2RealTranslate (y : R3) (g : R3L2RealScalar) :
    ‖r3L2RealTranslate y g‖ = ‖g‖ := by
  exact Lp.norm_compMeasurePreserving g (measurePreserving_r3TranslationMap y)

/-- The real `L²` translation orbit is continuous in the translation parameter. -/
theorem continuous_r3L2RealTranslate (g : R3L2RealScalar) :
    Continuous (fun y : R3 => r3L2RealTranslate y g) := by
  unfold r3L2RealTranslate
  have hg : Continuous (fun _ : R3 => g) := continuous_const
  exact hg.compMeasurePreservingLp continuous_r3TranslationMap
    (fun y => measurePreserving_r3TranslationMap y) (by simp)

/--
The real `L²`-valued Young integrand `f(y) τ_y g`, with `τ_y g(x)=g(x-y)`.
Unlike the earlier Schwartz-specific bridge, the scalar factor is only assumed continuous and
integrable; this is the regularity available for norm fields of Schwartz functions.
-/
def r3RealYoungL1L2Integrand
    (f : R3 → ℝ) (g : R3L2RealScalar) (y : R3) : R3L2RealScalar :=
  f y • r3L2RealTranslate y g

@[simp]
theorem norm_r3RealYoungL1L2Integrand
    (f : R3 → ℝ) (g : R3L2RealScalar) (y : R3) :
    ‖r3RealYoungL1L2Integrand f g y‖ = ‖f y‖ * ‖g‖ := by
  simp [r3RealYoungL1L2Integrand, norm_smul]

/-- The real Young integrand is continuous when the scalar factor is continuous. -/
theorem continuous_r3RealYoungL1L2Integrand
    {f : R3 → ℝ} (hf : Continuous f) (g : R3L2RealScalar) :
    Continuous (fun y : R3 => r3RealYoungL1L2Integrand f g y) := by
  unfold r3RealYoungL1L2Integrand
  exact hf.smul (continuous_r3L2RealTranslate g)

/-- The real Young integrand is Bochner integrable for a continuous `L¹` scalar factor. -/
theorem integrable_r3RealYoungL1L2Integrand
    {f : R3 → ℝ} (hf : Continuous f) (hfi : Integrable f)
    (g : R3L2RealScalar) :
    Integrable (fun y : R3 => r3RealYoungL1L2Integrand f g y) := by
  have hmajor : Integrable (fun y : R3 => ‖f y‖ * ‖g‖) :=
    hfi.norm.mul_const ‖g‖
  exact hmajor.mono'
    (continuous_r3RealYoungL1L2Integrand hf g).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [norm_r3RealYoungL1L2Integrand])

/-- The `L²`-valued Bochner convolution for a continuous real `L¹` factor and a real `L²` factor. -/
def r3RealYoungL1L2Convolution
    (f : R3 → ℝ) (g : R3L2RealScalar) : R3L2RealScalar :=
  ∫ y : R3, r3RealYoungL1L2Integrand f g y

/-- Young's `L¹ * L² → L²` estimate for continuous real scalar inputs. -/
theorem norm_r3RealYoungL1L2Convolution_le
    {f : R3 → ℝ} (hf : Continuous f) (hfi : Integrable f)
    (g : R3L2RealScalar) :
    ‖r3RealYoungL1L2Convolution f g‖ ≤ (∫ y : R3, ‖f y‖) * ‖g‖ := by
  calc
    ‖r3RealYoungL1L2Convolution f g‖ =
        ‖∫ y : R3, r3RealYoungL1L2Integrand f g y‖ := by
      rfl
    _ ≤ ∫ y : R3, ‖r3RealYoungL1L2Integrand f g y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : R3, ‖f y‖ * ‖g‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        norm_r3RealYoungL1L2Integrand f g y
    _ = (∫ y : R3, ‖f y‖) * ‖g‖ := by
      rw [integral_mul_const]

/--
Argument-order wrapper for the `L² * L¹` use case.  The underlying Bochner integral is still
written in the `L¹` variable, which is the orientation compatible with physical translations.
A later pointwise-identification bridge will combine this with commutativity of real convolution.
-/
def r3RealYoungL2L1Convolution
    (g : R3L2RealScalar) (f : R3 → ℝ) : R3L2RealScalar :=
  r3RealYoungL1L2Convolution f g

/-- Young's `L² * L¹ → L²` estimate, with arguments displayed in the order used by the left
frequency majorant. -/
theorem norm_r3RealYoungL2L1Convolution_le
    (g : R3L2RealScalar) {f : R3 → ℝ} (hf : Continuous f) (hfi : Integrable f) :
    ‖r3RealYoungL2L1Convolution g f‖ ≤ ‖g‖ * (∫ y : R3, ‖f y‖) := by
  rw [r3RealYoungL2L1Convolution]
  calc
    ‖r3RealYoungL1L2Convolution f g‖ ≤ (∫ y : R3, ‖f y‖) * ‖g‖ :=
      norm_r3RealYoungL1L2Convolution_le hf hfi g
    _ = ‖g‖ * (∫ y : R3, ‖f y‖) := by
      rw [mul_comm]

end

end MNS2
