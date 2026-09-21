import Bindings.InsertionFromData
import NSFormalization.Section4.A04.ZeroSolution

/-! Theorem 4.1(i) and the if direction of (ii), for the ambient class F_R.
The threshold is exactly `ThresholdAPI.formula` at spatial index zero.
As with InsertionFromData, do not combine this import with Bindings.Packet.
-/

noncomputable section
namespace BlowupDensity.Bindings

open Set Filter MeasureTheory
open Contracts.V1 Contracts.V1.Data
open scoped ENNReal Topology

/-- G5: the zero measurable Sobolev datum path has zero force norm. -/
theorem density_forceSobolevENorm_zero (q : ℝ≥0∞) (s : ℝ) :
    forceSobolevENorm q s (0 : SpaceTimeField) = 0 := by
  apply le_antisymm _ zero_le
  change (⨅ G : {G : ℝ → NSFormalization.Paper3.RealVectorSobolev s //
    IsSobolevPath s 0 G ∧ AEStronglyMeasurable G forceTimeMeasure},
      bochnerDatumENorm q s G.1) ≤ 0
  have hz : IsSobolevPath s 0 0 := by
    intro t _
    exact NSFormalization.Section4.D01.isSobolevDatum_zero s
  exact (iInf_le _ ⟨0, hz, aestronglyMeasurable_const⟩).trans
    (by simp [bochnerDatumENorm])

/-- Theorem 4.1(i): relative density for every fixed admissible initial datum. -/
theorem breakdownDenseR_of_subcritical :
    ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
      ∀ s : ℝ, s < 2 / q.toReal - 1 / 2 →
        ∀ a ∈ initialClassR, BreakdownDenseR ν a T q s := by
  intro ν T hν hT q hq s hs a ha g hg r hr
  by_cases hLife : maximalLifespanR ν a g ≤ ENNReal.ofReal T
  · refine ⟨g, ⟨hg, hLife⟩, ?_⟩
    simpa only [sub_self, density_forceSobolevENorm_zero] using hr
  · have hlong := lt_of_not_ge hLife
    obtain ⟨P, L, hLa, hLg, hLT⟩ :=
      insertionLifespanV2_of_data ν hν T hT a ha g hg hlong
    have hs' : s < L.family.scaling.thresholds.exponent q.toReal 0 := by
      simpa only [L.family.scaling.thresholds.formula, sub_zero] using hs
    have hsmall := (insertionFromData_forceConvergence L hLg q hq s hs').eventually
      (gt_mem_nhds hr)
    have hwindow : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) L.family.ε₀ :=
      Ioc_mem_nhdsGT L.family.eps_pos
    obtain ⟨ε, hε, hdist⟩ := (hwindow.and hsmall).exists
    refine ⟨L.family.force ε, ⟨?_, ?_⟩, hdist⟩
    · exact InsertionLifespan.memForceR_force L.family (hLg.symm ▸ hg) hε
    · exact (insertionFromData_lifespan L hLa hLT ε hε).le


end BlowupDensity.Bindings
