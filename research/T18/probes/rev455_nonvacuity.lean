import Tests.PeriodicInsertion

noncomputable section
namespace BlowupDensity.Review455

open Set
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusLocalTheory

example {ν : ℝ} {P : PacketImportAPI ν}
    {place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI}
    {scaling : BlowupDensity.T15.Draft.ScalingAPI P place}
    {a : SpatialField} {g : SpaceTimeField} {r δ : ℝ} {D : CutoffData}
    {reference : ClassicalSolutionT ν a g (place.T + δ)}
    {correction : BlowupDensity.T17.Spec.CorrectionAPI
      ν place reference.velocity r δ D}
    (A : BlowupDensity.T18.Spec.PeriodicInsertionAPI
      ν P place scaling a g r δ D reference correction) :
    ∃ ε : ℝ, ε ∈ Ioc (0 : ℝ) A.ε₀ :=
  ⟨A.ε₀, A.eps_pos, le_rfl⟩

end BlowupDensity.Review455
