import NSFormalization.Section4.A04.Forcing
import Mathlib.MeasureTheory.Group.LIntegral

/-! # Positive-time translation decreases the half-line forcing norm
The definition of `timeShift` is `research/A02/Spec.lean:157` verbatim.
The proof works directly with every measurable Sobolev datum in the infimum.
-/
noncomputable section
namespace NSFormalization.Section4.A04
open Set MeasureTheory
open NSFormalization.Section4.A02
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

def timeShift (t₀ : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z => f (z.1 + t₀, z.2)

/-- Positive translation discards the initial segment of the half-line. -/
theorem lintegral_enorm_shift_le {E : Type*} [NormedAddCommGroup E]
    (G : ℝ → E) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    (∫⁻ t in Ioi (0 : ℝ), ‖G (t + t₀)‖ₑ) ≤
      ∫⁻ t in Ioi (0 : ℝ), ‖G t‖ₑ := by
  rw [← lintegral_indicator measurableSet_Ioi,
    ← lintegral_indicator measurableSet_Ioi]
  calc
    (∫⁻ t, (Ioi (0 : ℝ)).indicator (fun t => ‖G (t + t₀)‖ₑ) t) ≤
        ∫⁻ t, (Ioi (0 : ℝ)).indicator (fun t => ‖G t‖ₑ) (t + t₀) := by
      apply lintegral_mono
      intro t
      by_cases ht : 0 < t
      · have hsum : 0 < t + t₀ := by linarith
        simp [Set.indicator_of_mem, ht, hsum]
      · simp [Set.indicator_of_notMem, ht]
    _ = _ := lintegral_add_right_eq_self _ t₀

/-- The shifted force uses only a tail of each datum's `L¹` norm. No force
regularity assumption is necessary, since the infimum ranges over measurable
paths and the translation preserves the nonnegative-time datum condition. -/
theorem forceSobolevENormL1_timeShift_le (s : ℝ) (f : SpaceTimeField)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    forceSobolevENormL1 s (timeShift t₀ f) ≤ forceSobolevENormL1 s f := by
  apply le_iInf
  rintro ⟨G, hpath, hmeas⟩
  let Gshift : ℝ → RealVectorSobolev s := fun t => G (t + t₀)
  have hshiftpath : IsSobolevPath s (timeShift t₀ f) Gshift := by
    intro t ht
    exact hpath (t + t₀) (by linarith)
  have hq : Measure.QuasiMeasurePreserving (fun t : ℝ => t + t₀)
      forceTimeMeasure forceTimeMeasure := by
    apply (measurePreserving_add_right (volume : Measure ℝ) t₀).quasiMeasurePreserving.restrict
    intro t ht
    show 0 < t + t₀
    have : 0 < t := ht
    linarith
  have hshiftmeas : AEStronglyMeasurable Gshift forceTimeMeasure :=
    hmeas.comp_quasiMeasurePreserving hq
  refine (iInf_le _ ⟨Gshift, hshiftpath, hshiftmeas⟩).trans ?_
  show eLpNorm Gshift 1 forceTimeMeasure ≤ eLpNorm G 1 forceTimeMeasure
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
  exact lintegral_enorm_shift_le G ht₀
end NSFormalization.Section4.A04
