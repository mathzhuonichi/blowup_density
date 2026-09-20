import research.R41D.Spec
import NSFormalization.Section4.A04.ZeroSolution

noncomputable section

namespace BlowupDensity.Review174

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.R41D.Draft
open scoped ENNReal

/-! Non-vacuity: every permitted ambient force class contains the zero force,
and the manuscript initial class contains the zero datum. -/

example : (0 : SpaceTimeField) ∈ forceClassR := by
  exact NSFormalization.Section4.A04.memForceR_zero

example : (0 : SpaceTimeField) ∈ forceClassCompact := by
  exact ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩

example : (0 : SpaceTimeField) ∈ forceClassRapid := by
  refine ⟨contDiffOn_const, ?_⟩
  intro N k
  refine ⟨0, ?_⟩
  intro t ht x
  simp

example : (0 : SpatialField) ∈ initialClassR := by
  exact NSFormalization.Section4.A04.zero_mem_initialClassR

theorem forceSobolevENorm_zero (q : ℝ≥0∞) (s : ℝ) :
    forceSobolevENorm q s (0 : SpaceTimeField) = 0 := by
  apply le_antisymm
  · let G : ℝ → NSFormalization.Paper3.RealVectorSobolev s := fun _ => 0
    have hG : IsSobolevPath s (0 : SpaceTimeField) G := by
      intro t ht
      exact NSFormalization.Section4.D01.isSobolevDatum_zero s
    have hmeas : AEStronglyMeasurable G forceTimeMeasure :=
      aestronglyMeasurable_const
    exact (iInf_le
      (fun H : {H : ℝ → NSFormalization.Paper3.RealVectorSobolev s //
        IsSobolevPath s (0 : SpaceTimeField) H ∧
          AEStronglyMeasurable H forceTimeMeasure} => bochnerDatumENorm q s H.1)
      ⟨G, hG, hmeas⟩).trans (by simp [bochnerDatumENorm, G])
  · exact bot_le

example (q : ℝ≥0∞) (s : ℝ) (radius : ℝ≥0∞) (hradius : 0 < radius) :
    forceSobolevENorm q s ((0 : SpaceTimeField) - 0) < radius := by
  simpa [forceSobolevENorm_zero] using hradius

/-! Exact conformance check for the sharp L² threshold.  The reviewer mutates
only `s < -1/2` to `s < 1/2`; assigning `A.densityL2` must then fail. -/

example {Y : Set SpaceTimeField} (A : RDensityAPI Y) :
    ∀ nu : ℝ, 0 < nu →
      ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < -1 / 2 →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ Y →
              ∀ radius : ℝ≥0∞, 0 < radius →
                ∃ f : SpaceTimeField,
                  f ∈ breakdownSetIn Y nu a T ∧
                  forceSobolevENormL2 s (f - g) < radius ∧
                  ((maximalLifespanR nu a g ≤ ENNReal.ofReal T ∧ f = g) ∨
                    (ENNReal.ofReal T < maximalLifespanR nu a g ∧
                      R42InsertedWitness nu T a g f)) :=
  A.densityL2

end BlowupDensity.Review174
