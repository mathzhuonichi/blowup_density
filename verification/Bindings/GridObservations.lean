import Contracts.V1.GridObservations
import Bindings.GridAssembly
import Bindings.ScalingHomogeneousClosed

/-! Register lane 258's R47 assembly after lane 255 discharges its sole input. -/

noncomputable section

namespace BlowupDensity.Bindings

open Set Filter Topology
open NavierStokes.ProblemStatement
open Contracts.V1.Data
open Contracts.V1.GridObservations
open NSFormalization.Section4.I03 (compactHomogeneousRealization)
open scoped ENNReal

/-- The implementation and contract records have identical fields but are
distinct structures, so transport the lane-258 witness field by field. -/
def gridFamilyAPI_of_rGridFamily
    {ν : ℝ} {a : SpatialField} {g : SpaceTimeField} {T δ : ℝ}
    {reference : ClassicalSolutionR ν a g (T + δ)}
    {n : ℕ} {grids : Fin n → Grid}
    (F : Research.R47.Draft.RGridFamily ν a g T δ reference n grids) :
    GridFamilyAPI ν a g T δ reference n grids where
  center := F.center
  radius := F.radius
  radius_pos := F.radius_pos
  containingCell := F.containingCell
  ε₀ := F.ε₀
  eps_pos := F.eps_pos
  force := F.force
  solution := F.solution
  force_mem := F.force_mem
  history := F.history
  forceDifference_compact := F.forceDifference_compact
  velocity_observations := F.velocity_observations
  force_observations := F.force_observations
  lifespan := F.lifespan
  energy_convergence := F.energy_convergence
  force_convergence := F.force_convergence
  velocity_support := F.velocity_support
  pressure_support := F.pressure_support
  force_support := F.force_support

/-- Lane 258's universal choice theorem in the registered structure type. -/
theorem gridObservations_choose :
    ∀ ν : ℝ, 0 < ν →
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ g : SpaceTimeField, MemForceR g →
    ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
    ∀ reference : ClassicalSolutionR ν a g (T + δ),
    ∀ n : ℕ, ∀ grids : Fin n → Grid,
      Nonempty (GridFamilyAPI ν a g T δ reference n grids) := by
  intro ν hν a ha g hg T hT δ hδ reference n grids
  obtain ⟨F⟩ := rGrid_choose_of_realization compactHomogeneousRealization
    ν hν a ha g hg T hT δ hδ reference n grids
  exact ⟨gridFamilyAPI_of_rGridFamily F⟩

/-- Complete, statement-faithful witness of Theorem 4.7. -/
theorem gridObservations : GridObservationsAPI where
  choose := gridObservations_choose

end BlowupDensity.Bindings
