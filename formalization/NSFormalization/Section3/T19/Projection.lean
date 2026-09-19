import NSFormalization.Section3.T19.DensityEngine

/-!
# T19 projection consequences

Fixed-initial density gives density in every force fibre of the extended
breakdown set.  The two projection identities then follow from concrete zero
members of the force and initial-data classes.
-/

noncomputable section

namespace NSFormalization.Section3.T19

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

/-- `ProjectionAPI.extendedProductDensity` (U10). -/
theorem extendedProductDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        ∀ a : SpatialField, a ∈ initialClassT →
          ∀ g : SpaceTimeField, g ∈ forceClassT →
            ∀ r : ℝ≥0∞, 0 < r →
              ∃ f : SpaceTimeField,
                (a, f) ∈ extendedBreakdownSetT ν T ∧
                  forceSobolevENormT 1 s (fun z => f z - g z) < r := by
  intro ν hν T hT s hs a ha g hg r hr
  obtain ⟨f, hf, hdist⟩ :=
    fixedInitialDensity a ha ν hν T hT s hs g hg r hr
  exact ⟨f, ⟨ha, hf.1, hf.2⟩, hdist⟩

/-- `ProjectionAPI.projectionOntoInitialData` (U11). -/
theorem projectionOntoInitialData :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst '' (extendedBreakdownSetT ν T) = initialClassT := by
  intro ν hν T hT
  ext a
  constructor
  · rintro ⟨⟨a, f⟩, haf, rfl⟩
    exact haf.1
  · intro ha
    have hzeroForce : (0 : SpaceTimeField) ∈ forceClassT := by
      refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
      · intro t _ht x i
        rfl
      · exact (show tsupport (0 : SpaceTimeField) ⊆
            (∅ : Set ℝ) ×ˢ (Set.univ : Set Space) by simp)
    obtain ⟨f, haf, _hdist⟩ := extendedProductDensity ν hν T hT
      0 (by norm_num) a ha 0 hzeroForce 1 (by norm_num)
    exact ⟨(a, f), haf, rfl⟩

/-- `ProjectionAPI.zeroInitialProjection` (U12). -/
theorem zeroInitialProjection :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst ''
          {p : SpatialField × SpaceTimeField |
            p ∈ extendedBreakdownSetT ν T ∧ p.1 = (fun _ => 0)} =
        {(fun _ => 0 : SpatialField)} := by
  intro ν hν T hT
  ext a
  constructor
  · rintro ⟨⟨a, f⟩, ⟨_haf, hazero⟩, rfl⟩
    simpa only [Set.mem_singleton_iff] using hazero
  · intro ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    have hzeroInitial : (0 : SpatialField) ∈ initialClassT := by
      refine ⟨contDiff_const, ?_, ?_⟩
      · intro x i
        rfl
      · intro x
        simp [spatialDivergence, spatialDerivative]
    have hzeroForce : (0 : SpaceTimeField) ∈ forceClassT := by
      refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
      · intro t _ht x i
        rfl
      · exact (show tsupport (0 : SpaceTimeField) ⊆
            (∅ : Set ℝ) ×ˢ (Set.univ : Set Space) by simp)
    obtain ⟨f, haf, _hdist⟩ := extendedProductDensity ν hν T hT
      0 (by norm_num) (0 : SpatialField) hzeroInitial 0 hzeroForce 1 (by norm_num)
    exact ⟨((0 : SpatialField), f), ⟨haf, rfl⟩, rfl⟩

end NSFormalization.Section3.T19
