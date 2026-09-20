import Tests.BoundaryInsertion

/-! Review mutation for lane 487b.

This changes the registered box theorem itself by deleting the `IsBoxDomain Ω`
hypothesis.  The production proof must then fail exactly where it needs the box
witness to obtain integration by parts. -/

namespace BlowupDensity.Review487

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.BoundaryInsertion
open Set

set_option linter.defProp false

def boundaryInsertionStatement'_without_box : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν)
    (place : DomainPlacementData P.toPacketAPI)
    (Ω : Set Space) (norms : BoundedDomainNorm.BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)),
    0 < δ → 0 < r →
      g ∈ forceClassOmega Ω → a ∈ initialClassOmega Ω →
      closure (Metric.ball place.x₀ r) ⊆ Metric.ball place.chartCenter place.chartRadius →
      closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω →
      ∃ (C : CorrectionAPI ν P.toPacketAPI) (D : CutoffData),
        C.T = place.T ∧ C.δ = δ ∧ C.x₀ = place.x₀ ∧ C.r = r ∧
        (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ Metric.ball place.x₀ r,
          C.v (t, x) = reference.velocity (t, x)) ∧
        D.θ = C.θ ∧ D.η = C.η ∧ D.plateau = C.plateau ∧
        D.θRadius = C.θRadius ∧ D.ε₀ = C.ε₀ ∧
        D.potential = C.potential ∧ D.correction = C.correction ∧
        Nonempty (BoundaryInsertionAPI ν P place Ω norms a g r δ D reference)

example : boundaryInsertionStatement'_without_box := by
  intro ν hν P place Ω norms a g r δ reference hδ hr hg ha hrball hball
  exact BlowupDensity.Bindings.BoundaryInsertion.Contract.boundaryInsertionStatement'_box_holds
    ν hν P place Ω norms a g r δ reference hδ hr hg ha hrball hball

end BlowupDensity.Review487
