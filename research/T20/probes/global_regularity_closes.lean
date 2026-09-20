import NSFormalization.Section3.T20.GlobalRegularity

/-!
Exact target-shape and non-vacuity probe for T20 unit U12
(`globalRegularity`, `prop:critical`).

The first two examples check that the spelling below is the canonical
`CriticalRegularityTAPI.globalRegularity` field and that lane 441 inhabits it
at `c = criticalSmallnessH1`.  The last example exhibits the zero force in
`forceClassT`, proves `criticalRho 0 = 0`, verifies the strict smallness
hypothesis at `ν = 1`, and applies the theorem.
-/

noncomputable section

namespace NSFormalization.Section3.T20.GlobalRegularityProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T20
open scoped ContDiff ENNReal

/-- The canonical `globalRegularity` field with its radius abstracted. -/
def globalRegularityFieldType (c : ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤

/-- The spelling above is literally the structure field. -/
example (API : CriticalRegularityTAPI) :
    globalRegularityFieldType API.c := API.globalRegularity

/-- Lane 441's theorem inhabits the canonical field at the U10b/U11 radius. -/
example : globalRegularityFieldType criticalSmallnessH1 := globalRegularity

/-- The theorem is non-vacuous at zero force: the force is admissible,
`criticalRho 0 = 0 < criticalSmallnessH1 * 1`, and the resulting from-rest
lifespan is infinite. -/
example :
    (0 : SpaceTimeField) ∈ forceClassT ∧
      criticalRho (0 : SpaceTimeField) = 0 ∧
      criticalRho (0 : SpaceTimeField) <
        ENNReal.ofReal (criticalSmallnessH1 * 1) ∧
      maximalLifespanT 1 (fun _ : Space ↦ 0) (0 : SpaceTimeField) = ⊤ := by
  have hg : (0 : SpaceTimeField) ∈ forceClassT :=
    ⟨contDiff_const, fun _ _ _ _ ↦ rfl, ∅, isCompact_empty, empty_subset _, by simp⟩
  have hρle : criticalRho (0 : SpaceTimeField) ≤ 0 := by
    show forceSobolevENormT 1 (1 / 2) (0 : SpaceTimeField) ≤ 0
    refine le_trans (iInf_le (fun G : {G : ℝ → PeriodicSobolev (1 / 2) //
        IsPeriodicSobolevPath (1 / 2) (0 : SpaceTimeField) G ∧
          AEStronglyMeasurable G forceTimeMeasure} ↦
      eLpNorm G.1 1 forceTimeMeasure)
      ⟨fun _ ↦ (0 : PeriodicSobolev (1 / 2)),
        fun t _ ↦ zero_isPeriodicDatum (1 / 2), aestronglyMeasurable_const⟩) ?_
    show eLpNorm (fun _ : ℝ ↦ (0 : PeriodicSobolev (1 / 2)))
        1 forceTimeMeasure ≤ 0
    exact le_of_eq eLpNorm_zero'
  have hρ : criticalRho (0 : SpaceTimeField) = 0 := le_antisymm hρle bot_le
  have hsmall : criticalRho (0 : SpaceTimeField) <
      ENNReal.ofReal (criticalSmallnessH1 * 1) := by
    rw [hρ]
    exact ENNReal.ofReal_pos.2 (by simpa using criticalSmallnessH1_pos)
  exact ⟨hg, hρ, hsmall,
    globalRegularity 1 zero_lt_one (0 : SpaceTimeField) hg hsmall⟩

end NSFormalization.Section3.T20.GlobalRegularityProbe
