import Mathlib.MeasureTheory.Function.L2Space
import Formal.R3LerayComplexDivergenceBridge

namespace MNS2

open MeasureTheory Filter

noncomputable section

/-- The complex Leray symbol applied pointwise to a bundled Fourier-side `L²` velocity. -/
def r3LerayPointwiseAction (f : R3L2Velocity) : R3 → R3C :=
  fun ξ => r3LeraySymbolComplex ξ (f ξ)

/-- The coordinatewise complex embedding of the real frequency vector is continuous. -/
theorem continuous_r3FrequencyVectorComplex :
    Continuous r3FrequencyVectorComplex := by
  unfold r3FrequencyVectorComplex
  fun_prop

/-- The pointwise complex Leray action is strongly measurable almost everywhere. -/
theorem aestronglyMeasurable_r3LerayPointwiseAction
    (f : R3L2Velocity) :
    AEStronglyMeasurable (r3LerayPointwiseAction f) volume := by
  unfold r3LerayPointwiseAction
  rw [show
    (fun ξ => r3LeraySymbolComplex ξ (f ξ)) =
      fun ξ =>
        f ξ -
          (inner ℂ (r3FrequencyVectorComplex ξ) (f ξ) /
            (((‖r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) •
            r3FrequencyVectorComplex ξ by
      funext ξ
      exact r3LeraySymbolComplex_apply ξ (f ξ)]
  have hfreq : AEStronglyMeasurable r3FrequencyVectorComplex volume :=
    continuous_r3FrequencyVectorComplex.aestronglyMeasurable
  have hf : AEStronglyMeasurable (fun ξ : R3 => f ξ) volume :=
    Lp.aestronglyMeasurable f
  have hinner :
      AEStronglyMeasurable
        (fun ξ : R3 => inner ℂ (r3FrequencyVectorComplex ξ) (f ξ)) volume :=
    hfreq.inner hf
  have hden :
      AEStronglyMeasurable
        (fun ξ : R3 => (((‖r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) volume := by
    fun_prop
  have hquot :
      AEStronglyMeasurable
        (fun ξ : R3 =>
          inner ℂ (r3FrequencyVectorComplex ξ) (f ξ) /
            (((‖r3FrequencyVectorComplex ξ‖ ^ 2 : ℝ) : ℂ))) volume :=
    (hinner.aemeasurable.div hden.aemeasurable).aestronglyMeasurable
  exact hf.sub (hquot.smul hfreq)

/-- Fiberwise contraction shows that the pointwise complex Leray action still belongs to `L²`. -/
theorem memLp_r3LerayPointwiseAction
    (f : R3L2Velocity) :
    MemLp (r3LerayPointwiseAction f) 2 volume := by
  exact (Lp.memLp f).of_le
    (aestronglyMeasurable_r3LerayPointwiseAction f)
    (ae_of_all _ fun ξ => norm_r3LeraySymbolComplex_le ξ (f ξ))

/-- The explicit complex Leray matrix action, packaged as an element of `L²(R³; ℂ³)`. -/
def r3LerayPointwiseL2 (f : R3L2Velocity) : R3L2Velocity :=
  (memLp_r3LerayPointwiseAction f).toLp (r3LerayPointwiseAction f)

/-- The bundled `L²` object agrees almost everywhere with the explicit pointwise Leray symbol. -/
theorem r3LerayPointwiseL2_ae
    (f : R3L2Velocity) :
    r3LerayPointwiseL2 f =ᵐ[volume]
      fun ξ => r3LeraySymbolComplex ξ (f ξ) := by
  exact MemLp.coeFn_toLp (memLp_r3LerayPointwiseAction f)

end

end MNS2
