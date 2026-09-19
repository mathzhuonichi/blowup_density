import Tests.PeriodicInsertion

noncomputable section
namespace BlowupDensity.Review455

open Set
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusLocalTheory

variable {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI
      ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT)

local notation "A" =>
  Bindings.PeriodicInsertion.periodicInsertion
    P place scaling a g r δ D reference correction hδ hg ha

-- Deliberate substantive mutation: widen the quiet-history interval from
-- `t ≤ T - 2 * ε ^ 2` to `t ≤ T - ε ^ 2`.
example : ∀ ε ∈ Ioc (0 : ℝ) (A).ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ place.T - ε ^ 2 → ∀ x : Space,
      (A).velocity ε (t, x) = reference.velocity (t, x) := by
  exact (A).history

end BlowupDensity.Review455
