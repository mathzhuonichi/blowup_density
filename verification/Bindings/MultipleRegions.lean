import Contracts.V1.MultipleRegions
import Bindings.PacketImport
import Bindings.Scaling3
import NSFormalization.Section3.T24.MultipleAssembly

/-! Binding of the packet-indexed T24b contract to the canonical raw-field
assembly. The four restated definitions have `rfl` drift guards; the three
structure types are transported field by field. -/
noncomputable section
namespace BlowupDensity.Bindings.MultipleRegions

open Set MeasureTheory
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData
open Contracts.V1.TorusLocalTheory Contracts.V1.Scaling3
open scoped ContDiff ENNReal BigOperators Topology

/-! ## Definitional drift guards -/

theorem finiteVelocitySum_eq : @Contracts.V1.finiteVelocitySum =
    @NSFormalization.Section3.T24.finiteVelocitySum := rfl

theorem finitePressureSum_eq : @Contracts.V1.finitePressureSum =
    @NSFormalization.Section3.T24.finitePressureSum := rfl

theorem finiteForceSum_eq : @Contracts.V1.finiteForceSum =
    @NSFormalization.Section3.T24.finiteForceSum := rfl

theorem speedUnboundedAtOn_eq : Contracts.V1.SpeedUnboundedAtOn =
    NSFormalization.Section3.T24.SpeedUnboundedAtOn := rfl

/-! ## Fieldwise structure transport -/

/-- Contract record to canonical raw-field record. -/
def ofContract {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : Contracts.V1.MultipleRegionsAPI P T c r) :
    NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν)
      P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r where
  T_pos := a.T_pos
  N_pos := a.N_pos
  regionRadius_pos := a.regionRadius_pos
  region_interior := a.region_interior
  regions_disjoint := a.regions_disjoint
  placement := fun j ↦ Scaling3.placementOfSpec (a.placement j)
  placement_time := a.placement_time
  placement_chart := a.placement_chart
  scaling := fun j ↦ Scaling3.scalingOfSpec (a.scaling j)
  ε := a.ε
  eps_admissible := a.eps_admissible
  eps_time := a.eps_time
  component := fun j ↦ TorusLocalTheory.ofContract (a.component j)
  component_pin := a.component_pin
  component_support := a.component_support
  component_force_support := a.component_force_support
  assembled_velocity := a.assembled_velocity
  assembled_velocity_formula := a.assembled_velocity_formula
  assembled_pressure := a.assembled_pressure
  assembled_pressure_formula := a.assembled_pressure_formula
  assembled_force := a.assembled_force
  assembled_force_formula := a.assembled_force_formula
  solution := TorusLocalTheory.ofContract a.solution
  solution_pin := a.solution_pin
  force_mem := a.force_mem
  rest := a.rest
  region_agreement := a.region_agreement
  region_blowup := a.region_blowup
  energy_bound := a.energy_bound
  dissipation_bound := a.dissipation_bound

/-- Canonical raw-field record to the packet-indexed contract record. -/
def toContract {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν)
      P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    Contracts.V1.MultipleRegionsAPI P T c r where
  T_pos := a.T_pos
  N_pos := a.N_pos
  regionRadius_pos := a.regionRadius_pos
  region_interior := a.region_interior
  regions_disjoint := a.regions_disjoint
  placement := fun j ↦ Scaling3.placementToSpec (a.placement j)
  placement_time := a.placement_time
  placement_chart := a.placement_chart
  scaling := fun j ↦ Scaling3.scalingToSpec (a.scaling j)
  ε := a.ε
  eps_admissible := a.eps_admissible
  eps_time := a.eps_time
  component := fun j ↦ TorusLocalTheory.toContract (a.component j)
  component_pin := a.component_pin
  component_support := a.component_support
  component_force_support := a.component_force_support
  assembled_velocity := a.assembled_velocity
  assembled_velocity_formula := a.assembled_velocity_formula
  assembled_pressure := a.assembled_pressure
  assembled_pressure_formula := a.assembled_pressure_formula
  assembled_force := a.assembled_force
  assembled_force_formula := a.assembled_force_formula
  solution := TorusLocalTheory.toContract a.solution
  solution_pin := a.solution_pin
  force_mem := a.force_mem
  rest := a.rest
  region_agreement := a.region_agreement
  region_blowup := a.region_blowup
  energy_bound := a.energy_bound
  dissipation_bound := a.dissipation_bound

theorem to_of {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : Contracts.V1.MultipleRegionsAPI P T c r) :
    toContract (ofContract a) = a := rfl

theorem of_to {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν)
      P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ofContract (toContract a) = a := rfl

/-! ## Assembly from the registered packet projections -/

def regionsData {ν : ℝ} (P : PacketImportAPI ν) (T : ℝ) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N) (c : Fin N → Space) (r : Fin N → ℝ)
    (hr : ∀ j, 0 < r j)
    (hQ : ∀ j, closure (Metric.ball (c j) (r j)) ⊆ interior fundamentalCube)
    (hd : Pairwise (fun i j ↦
      Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))) :
    NSFormalization.Section3.T24.RegionsData ν P.velocity P.pressure P.force
      P.carrier P.energyBound P.dissipationBound where
  packet :=
    { extension_smooth := P.velocity_extension_smooth
      carrier_compact := P.carrier_compact
      support := P.velocity_support
      square_int := P.square_integrable
      zero_initial := P.zero_initial_velocity
      energy_isLUB := P.energy_isLUB
      dissipation_int := P.dissipation_integrable
      dissipation_eq := P.dissipation_eq }
  pressure_support := P.pressure_support
  pressure_smooth := P.pressure_extension_smooth
  force_smooth := P.force_smooth
  force_support := P.force_support
  force_zero := P.force_zero_nonpos
  momentum := P.extension_navier_stokes
  divergence := P.extension_divergence_free
  blowup := P.speed_unbounded
  T := T
  hT := hT
  N := N
  N_pos := hN
  regionCenter := c
  regionRadius := r
  regionRadius_pos := hr
  region_interior := hQ
  regions_disjoint := hd

/-- The registered thirty-field record for any imported packet and prescribed
finite disjoint family of interior balls. -/
def multipleRegions {ν : ℝ} (P : PacketImportAPI ν) (T : ℝ) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N) (c : Fin N → Space) (r : Fin N → ℝ)
    (hr : ∀ j, 0 < r j)
    (hQ : ∀ j, closure (Metric.ball (c j) (r j)) ⊆ interior fundamentalCube)
    (hd : Pairwise (fun i j ↦
      Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))) :
    Contracts.V1.MultipleRegionsAPI P T c r :=
  toContract (NSFormalization.Section3.T24.multipleRegionsAPI
    (regionsData P T hT N hN c r hr hQ hd))

/-- The registered packet-indexed existence statement. -/
theorem multipleRegionsStatement_holds : Contracts.V1.multipleRegionsStatement := by
  intro _ν _hν P T hT N hN c r hr hQ hd
  exact ⟨multipleRegions P T hT N hN c r hr hQ hd⟩

end BlowupDensity.Bindings.MultipleRegions

namespace BlowupDensity.Bindings

/-- Public T24b record constructor. -/
def multipleRegions {ν : ℝ} (P : Contracts.V1.PacketImportAPI ν)
    (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 0 < N)
    (c : Fin N → Contracts.V1.Space) (r : Fin N → ℝ)
    (hr : ∀ j, 0 < r j)
    (hQ : ∀ j, closure (Metric.ball (c j) (r j)) ⊆
      interior Contracts.V1.fundamentalCube)
    (hd : Pairwise (fun i j ↦
      Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))) :
    Contracts.V1.MultipleRegionsAPI P T c r :=
  MultipleRegions.multipleRegions P T hT N hN c r hr hQ hd

/-- Public proof of `prop:multiple`. -/
theorem multipleRegionsStatement_holds : Contracts.V1.multipleRegionsStatement :=
  MultipleRegions.multipleRegionsStatement_holds

end BlowupDensity.Bindings
