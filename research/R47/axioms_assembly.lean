import Bindings.GridAssembly

open BlowupDensity.Contracts.V1.Data BlowupDensity.Bindings
open BlowupDensity.Research.R47.Draft
open NSFormalization.Section4
open I03 (CompactHomogeneousRealization)

#print axioms grid_power_limit
#print axioms grid_mixed_add
#print axioms grid_homogeneous_add
#print axioms grid_mixed_limit
#print axioms grid_homogeneous_limit
#print axioms rGridFamily_of_data
#print axioms rGrid_choose_of_realization

-- Concrete zero reference, positive viscosity and horizon, empty grid family.
example (hreal : CompactHomogeneousRealization) :
    Nonempty (RGridFamily 1 0 0 1 1
      (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num)))
      0 Fin.elim0) :=
  rGrid_choose_of_realization hreal 1 (by norm_num) 0 A04.zero_mem_initialClassR
    0 A04.memForceR_zero 1 (by norm_num) 1 (by norm_num) _ 0 Fin.elim0

-- The same non-vacuous data, now with one complete unit Cartesian grid.
example (hreal : CompactHomogeneousRealization) :
    Nonempty (RGridFamily 1 0 0 1 1
      (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num)))
      1 (fun _ => ⟨0, fun _ => 1, fun _ => by norm_num⟩)) :=
  rGrid_choose_of_realization hreal 1 (by norm_num) 0 A04.zero_mem_initialClassR
    0 A04.memForceR_zero 1 (by norm_num) 1 (by norm_num) _ 1 _

-- Public API check in the frozen Data vocabulary.
example (hreal : CompactHomogeneousRealization) : RGridAPI :=
  ⟨rGrid_choose_of_realization hreal⟩
