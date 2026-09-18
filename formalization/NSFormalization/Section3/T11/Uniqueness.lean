import NSFormalization.Section3.T11.FlowConversion

/-!
# Uniqueness and realized-horizon order for periodic classical solutions

The fieldwise conversion to the older Paper 1 `Flow` structure exposes its
unconditional common-interval uniqueness theorems.  The T10 Haar pressure
gauge is the same normalization as Paper 1's cube integral by
`integral_torusLift`.  The lifespan statement is independent of that
conversion: a realized T10 horizon is one of the terms in the defining
supremum of `maximalLifespanT`.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Paper1
open NSFormalization.Paper1.PeriodicLocalLifespan
open scoped ENNReal

/-- The `PeriodicLocalTheoryAPI.velocity_unique` field, verbatim. -/
theorem velocity_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x) := by
  intro ν hν a _ha f _hf T₁ T₂ u₁ u₂
  exact flow_velocity_agree_on_common_interval hν (toFlow u₁) (toFlow u₂)

/-- The `PeriodicLocalTheoryAPI.pressure_unique` field, verbatim. -/
theorem pressure_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.pressure (t, x) = u₂.pressure (t, x) := by
  intro ν hν a _ha f _hf T₁ T₂ u₁ u₂
  have normalized (w : ClassicalSolutionT ν a f T₁) :
      IsNormalized (toFlow w) := by
    intro t ht
    rw [← integral_torusLift]
    exact w.pressure_gauge t ht
  have normalized₂ : IsNormalized (toFlow u₂) := by
    intro t ht
    rw [← integral_torusLift]
    exact u₂.pressure_gauge t ht
  exact fun t ht x ↦ (normalized_flows_agree hν (toFlow u₁) (toFlow u₂)
    (normalized u₁) normalized₂ t ht x).2

/-- The `PeriodicLocalTheoryAPI.horizon_le_lifespan` field, verbatim, with
the preceding `solution` field supplied explicitly. -/
theorem horizon_le_lifespan
    {horizon : ℝ → SpatialField → SpaceTimeField → ℝ}
    (solution : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ClassicalSolutionT ν a f (horizon ν a f)) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanT ν a f := by
  intro ν hν a ha f hf
  let w := solution ν hν a ha f hf
  exact le_iSup_of_le (horizon ν a f) (le_iSup_of_le ⟨w⟩ le_rfl)

end NSFormalization.Section3.T11
