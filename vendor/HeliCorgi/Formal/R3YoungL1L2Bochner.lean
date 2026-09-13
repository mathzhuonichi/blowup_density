import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.CompactOpen
import Formal.R3H2WeightedConvolutionKernel

namespace MNS2

open MeasureTheory

noncomputable section

/-- The physical translation map `x ↦ x - y` as a continuous self-map of `R³`. -/
def r3TranslationMap (y : R3) : C(R3, R3) where
  toFun x := x - y
  continuous_toFun := continuous_id.sub continuous_const

/-- The family `y ↦ (x ↦ x-y)` is continuous in the compact-open topology. -/
theorem continuous_r3TranslationMap :
    Continuous (fun y : R3 => r3TranslationMap y) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : R3 × R3 => p.2 - p.1)
  exact continuous_snd.sub continuous_fst

/-- Physical translations preserve Lebesgue volume on `R³`. -/
theorem measurePreserving_r3TranslationMap (y : R3) :
    MeasurePreserving (r3TranslationMap y) volume volume := by
  simpa [r3TranslationMap] using
    (measurePreserving_sub_right (volume : Measure R3) y)

/-- Translation of an `R³` `L²` velocity field by `y`, defined directly through composition with
the measure-preserving physical translation `x ↦ x-y`. -/
def r3L2Translate (y : R3) (g : R3L2Velocity) : R3L2Velocity :=
  Lp.compMeasurePreserving (r3TranslationMap y)
    (measurePreserving_r3TranslationMap y) g

@[simp]
theorem norm_r3L2Translate (y : R3) (g : R3L2Velocity) :
    ‖r3L2Translate y g‖ = ‖g‖ := by
  exact Lp.norm_compMeasurePreserving g (measurePreserving_r3TranslationMap y)

/-- The `L²` translation orbit is continuous in the translation parameter. -/
theorem continuous_r3L2Translate (g : R3L2Velocity) :
    Continuous (fun y : R3 => r3L2Translate y g) := by
  unfold r3L2Translate
  have hg : Continuous (fun _ : R3 => g) := continuous_const
  exact hg.compMeasurePreservingLp continuous_r3TranslationMap
    (fun y => measurePreserving_r3TranslationMap y) (by simp)

/--
The `L²`-valued Young integrand `f(y) τ_y g`, with `τ_y g(x) = g(x-y)`.

For the current Navier--Stokes application the scalar factor will be one weighted Fourier
coordinate and the vector factor one weighted Fourier velocity field.
-/
def r3YoungL2Integrand
    (f : R3SchwartzScalar) (g : R3L2Velocity) (y : R3) : R3L2Velocity :=
  f y • r3L2Translate y g

@[simp]
theorem norm_r3YoungL2Integrand
    (f : R3SchwartzScalar) (g : R3L2Velocity) (y : R3) :
    ‖r3YoungL2Integrand f g y‖ = ‖f y‖ * ‖g‖ := by
  simp [r3YoungL2Integrand, norm_smul]

/-- The `L²`-valued Young integrand is continuous, hence strongly measurable. -/
theorem continuous_r3YoungL2Integrand
    (f : R3SchwartzScalar) (g : R3L2Velocity) :
    Continuous (fun y : R3 => r3YoungL2Integrand f g y) := by
  unfold r3YoungL2Integrand
  have hf : Continuous (fun y : R3 => f y) := f.continuous
  have hg : Continuous (fun y : R3 => r3L2Translate y g) :=
    continuous_r3L2Translate g
  exact hf.smul hg

/-- The `L²`-valued Young integrand is Bochner integrable for a Schwartz scalar input. -/
theorem integrable_r3YoungL2Integrand
    (f : R3SchwartzScalar) (g : R3L2Velocity) :
    Integrable (fun y : R3 => r3YoungL2Integrand f g y) := by
  have hmajor : Integrable (fun y : R3 => ‖f y‖ * ‖g‖) :=
    (Integrable.norm f.integrable).mul_const ‖g‖
  exact hmajor.mono'
    (continuous_r3YoungL2Integrand f g).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [norm_r3YoungL2Integrand])

/--
The `L²`-valued convolution obtained as a Bochner integral of translated `L²` fields.

This construction avoids choosing pointwise representatives of the `L²` input.  A later bridge can
identify it with the ordinary convolution when the second input is also Schwartz.
-/
def r3YoungConvolutionL2
    (f : R3SchwartzScalar) (g : R3L2Velocity) : R3L2Velocity :=
  ∫ y : R3, r3YoungL2Integrand f g y

/--
Young's `L¹ * L² → L²` estimate for the Bochner convolution with a Schwartz scalar factor.
The first factor on the right is exactly the physical `L¹` norm of the scalar Schwartz function.
-/
theorem norm_r3YoungConvolutionL2_le
    (f : R3SchwartzScalar) (g : R3L2Velocity) :
    ‖r3YoungConvolutionL2 f g‖ ≤ (∫ y : R3, ‖f y‖) * ‖g‖ := by
  calc
    ‖r3YoungConvolutionL2 f g‖ =
        ‖∫ y : R3, r3YoungL2Integrand f g y‖ := by
      rfl
    _ ≤ ∫ y : R3, ‖r3YoungL2Integrand f g y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : R3, ‖f y‖ * ‖g‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        norm_r3YoungL2Integrand f g y
    _ = (∫ y : R3, ‖f y‖) * ‖g‖ := by
      rw [integral_mul_const]

end

end MNS2
