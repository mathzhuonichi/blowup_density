import Tests.GridObservations

/-! Transitive axiom audit and concrete conformance probes for R47 V1. -/

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.GridObservations
open BlowupDensity.Bindings
open NSFormalization.Section4

#print axioms I03.compactHomogeneousRealization
#print axioms rGridFamily_of_data
#print axioms rGrid_choose_of_realization
#print axioms gridFamilyAPI_of_rGridFamily
#print axioms gridObservations_choose
#print axioms gridObservations
#print axioms BlowupDensity.Tests.checkedGridObservations

noncomputable section

namespace GridObservationsContractConformance

/-- The checked contract exposes exactly the reconciled `RGridAPI.choose` type. -/
theorem choose :
    ∀ ν : ℝ, 0 < ν →
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ g : SpaceTimeField, MemForceR g →
    ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
    ∀ reference : ClassicalSolutionR ν a g (T + δ),
    ∀ n : ℕ, ∀ grids : Fin n → Grid,
      Nonempty (GridFamilyAPI ν a g T δ reference n grids) :=
  BlowupDensity.Tests.checkedGridObservations.choose

/-- A concrete positive-data witness for the empty prescribed grid family. -/
theorem emptyGridWitness :
    Nonempty (GridFamilyAPI 1 0 0 1 1
      (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num)))
      0 Fin.elim0) :=
  choose 1 (by norm_num) 0 A04.zero_mem_initialClassR
    0 A04.memForceR_zero 1 (by norm_num) 1 (by norm_num) _ 0 Fin.elim0

/-- The same data with one complete unit Cartesian grid. -/
theorem unitGridWitness :
    Nonempty (GridFamilyAPI 1 0 0 1 1
      (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num)))
      1 (fun _ => ⟨0, fun _ => 1, fun _ => by norm_num⟩)) :=
  choose 1 (by norm_num) 0 A04.zero_mem_initialClassR
    0 A04.memForceR_zero 1 (by norm_num) 1 (by norm_num) _ 1 _

#print axioms choose
#print axioms emptyGridWitness
#print axioms unitGridWitness

end GridObservationsContractConformance
