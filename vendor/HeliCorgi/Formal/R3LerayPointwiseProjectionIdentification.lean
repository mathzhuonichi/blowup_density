import Mathlib.MeasureTheory.Function.L2Space
import Formal.R3LerayPointwiseL2

namespace MNS2

open MeasureTheory Filter FourierTransform
open scoped FourierTransform

noncomputable section

local instance r3L2FrequencySolenoidalSubmodule_completeSpace_pointwise :
    CompleteSpace r3L2FrequencySolenoidalSubmodule := by
  change CompleteSpace r3NormalizedDivergenceFrequencyAux.ker
  infer_instance

/-- The explicit pointwise Leray `L²` package belongs to the frequency-side solenoidal kernel. -/
theorem r3LerayPointwiseL2_mem_frequency_solenoidal
    (f : R3L2Velocity) :
    r3LerayPointwiseL2 f ∈ r3L2FrequencySolenoidalSubmodule := by
  rw [mem_r3L2FrequencySolenoidalSubmodule_iff]
  apply Lp.ext
  filter_upwards
    [r3NormalizedDivergenceFrequencyAux_ae (r3LerayPointwiseL2 f),
      r3LerayPointwiseL2_ae f,
      Lp.coeFn_zero (α := R3) ℂ 2 (volume : Measure R3)]
    with ξ hdiv hpoint hzero
  rw [hdiv, hpoint, r3NormalizedDivergencePointwise_r3LeraySymbolComplex]
  exact hzero.symm

/-- A frequency-side solenoidal `L²` field is pointwise in the complex transverse fiber almost everywhere. -/
theorem ae_mem_r3ComplexSolenoidalFiber_of_frequency_solenoidal
    {g : R3L2Velocity} (hg : g ∈ r3L2FrequencySolenoidalSubmodule) :
    ∀ᵐ ξ ∂(volume : Measure R3), g ξ ∈ r3ComplexSolenoidalFiber ξ := by
  have hg0 : r3NormalizedDivergenceFrequencyAux g = 0 :=
    (mem_r3L2FrequencySolenoidalSubmodule_iff g).1 hg
  have hzero :
      ((r3NormalizedDivergenceFrequencyAux g : R3L2ScalarAux) : R3 → ℂ) =ᵐ[volume]
        (0 : R3 → ℂ) := by
    rw [hg0]
    exact Lp.coeFn_zero (α := R3) ℂ 2 (volume : Measure R3)
  have hdiv :
      (fun ξ => r3NormalizedDivergencePointwise ξ (g ξ)) =ᵐ[volume]
        (0 : R3 → ℂ) :=
    (r3NormalizedDivergenceFrequencyAux_ae g).symm.trans hzero
  filter_upwards [hdiv] with ξ hξ
  exact
    (mem_r3ComplexSolenoidalFiber_iff_normalizedDivergencePointwise_eq_zero ξ (g ξ)).2 hξ

/-- The residual from the explicit pointwise Leray action is orthogonal to every frequency-side solenoidal field. -/
theorem inner_sub_r3LerayPointwiseL2_eq_zero
    (f g : R3L2Velocity) (hg : g ∈ r3L2FrequencySolenoidalSubmodule) :
    inner ℂ (f - r3LerayPointwiseL2 f) g = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hpoint :
      ∀ᵐ ξ ∂(volume : Measure R3),
        inner ℂ
          (f ξ - r3LeraySymbolComplex ξ (f ξ))
          (g ξ) = 0 := by
    filter_upwards [ae_mem_r3ComplexSolenoidalFiber_of_frequency_solenoidal hg] with ξ hgξ
    change
      inner ℂ
        (f ξ - (r3ComplexSolenoidalFiber ξ).starProjection (f ξ))
        (g ξ) = 0
    exact
      Submodule.starProjection_inner_eq_zero
        (K := r3ComplexSolenoidalFiber ξ) (f ξ) (g ξ) hgξ
  calc
    ∫ ξ : R3, inner ℂ ((f - r3LerayPointwiseL2 f) ξ) (g ξ) ∂volume =
        ∫ ξ : R3, inner ℂ (f ξ - r3LeraySymbolComplex ξ (f ξ)) (g ξ) ∂volume := by
          apply integral_congr_ae
          filter_upwards
            [Lp.coeFn_sub f (r3LerayPointwiseL2 f), r3LerayPointwiseL2_ae f]
            with ξ hsub hpointwise
          simp only [hsub, hpointwise, Pi.sub_apply]
    _ = ∫ _ξ : R3, (0 : ℂ) ∂volume := integral_congr_ae hpoint
    _ = 0 := by simp

/-- The abstract frequency-side orthogonal projector is exactly the bundled pointwise complex Leray action. -/
theorem r3LerayL2FrequencyOperator_eq_pointwise
    (f : R3L2Velocity) :
    r3LerayL2FrequencyOperator f = r3LerayPointwiseL2 f := by
  change r3L2FrequencySolenoidalSubmodule.starProjection f = r3LerayPointwiseL2 f
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact r3LerayPointwiseL2_mem_frequency_solenoidal f
  · intro g hg
    exact inner_sub_r3LerayPointwiseL2_eq_zero f g hg

/-- Almost-everywhere matrix-multiplier realization of the frequency-side `L²` Leray projector. -/
theorem r3LerayL2FrequencyOperator_ae
    (f : R3L2Velocity) :
    r3LerayL2FrequencyOperator f =ᵐ[volume]
      fun ξ => r3LeraySymbolComplex ξ (f ξ) := by
  rw [r3LerayL2FrequencyOperator_eq_pointwise f]
  exact r3LerayPointwiseL2_ae f

/-- The physical `L²` Leray projector has the expected explicit complex Fourier multiplier almost everywhere. -/
theorem fourier_r3LerayL2Operator_ae
    (f : R3L2Velocity) :
    ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) (r3LerayL2Operator f) : R3 → R3C) =ᵐ[volume]
      fun ξ =>
        r3LeraySymbolComplex ξ
          (((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) f) ξ) := by
  have hFourier :
      (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) (r3LerayL2Operator f) =
        r3LerayL2FrequencyOperator
          ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) f) := by
    exact fourier_r3LerayL2Operator f
  rw [hFourier]
  exact
    r3LerayL2FrequencyOperator_ae
      ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) f)

end

end MNS2
