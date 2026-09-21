import Contracts.V2.MultipleRegions
import Bindings.MultipleRegions
import Bindings.BoundaryInsertion
import NSFormalization.Section3.T24.MultipleOmegaAssembly

/-! Raw packet projections and fieldwise transport for both branches of Proposition 3.16. -/
noncomputable section
namespace BlowupDensity.Bindings.MultipleRegionsV2
open Set MeasureTheory
open Contracts.V1 Contracts.V1.Data Contracts.V1.BoundaryInsertion
open scoped ContDiff ENNReal BigOperators Topology

/-- Restricted physical norms retain their exact canonical definitions. -/
theorem energyEssSupOmega_eq : Contracts.V2.MultipleRegions.energyEssSupOmega =
    NSFormalization.Section3.T24.energyEssSupOmega := rfl

theorem energyGradientOmega_eq : Contracts.V2.MultipleRegions.energyGradientOmega =
    NSFormalization.Section3.T24.energyGradientOmega := rfl

/-- Contract record to canonical raw-field record. -/
def ofContract {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {Ω : Set Space} {hΩ : IsBoundedBoxOrSmoothDomain Ω}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : Contracts.V2.MultipleRegions.MultipleRegionsOmegaAPI P T Ω hΩ c r) :
    NSFormalization.Section3.T24.MultipleRegionsOmegaAPI (ν := ν)
      P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T Ω hΩ c r where
  T_pos := a.T_pos
  N_pos := a.N_pos
  regionRadius_pos := a.regionRadius_pos
  region_interior := a.region_interior
  regions_disjoint := a.regions_disjoint
  placement := fun j ↦ BoundaryInsertion.Contract.placeTo (a.placement j)
  placement_time := a.placement_time
  placement_chart := a.placement_chart
  ε := a.ε
  eps_admissible := a.eps_admissible
  eps_time := a.eps_time
  component := fun j ↦ BoundaryInsertion.Contract.solutionTo (a.component j)
  component_pin := a.component_pin
  component_support := a.component_support
  component_force_support := a.component_force_support
  assembled_velocity := a.assembled_velocity
  assembled_velocity_formula := a.assembled_velocity_formula
  assembled_pressure := a.assembled_pressure
  assembled_pressure_formula := a.assembled_pressure_formula
  assembled_force := a.assembled_force
  assembled_force_formula := a.assembled_force_formula
  solution := BoundaryInsertion.Contract.solutionTo a.solution
  solution_pin := a.solution_pin
  force_mem := a.force_mem
  rest := a.rest
  region_agreement := a.region_agreement
  region_blowup := a.region_blowup
  energy_bound := a.energy_bound
  dissipation_bound := a.dissipation_bound
  no_slip := a.no_slip

/-- Canonical raw-field record to the packet-indexed contract record. -/
def toContract {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {Ω : Set Space} {hΩ : IsBoundedBoxOrSmoothDomain Ω}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : NSFormalization.Section3.T24.MultipleRegionsOmegaAPI (ν := ν)
      P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T Ω hΩ c r) :
    Contracts.V2.MultipleRegions.MultipleRegionsOmegaAPI P T Ω hΩ c r where
  T_pos := a.T_pos
  N_pos := a.N_pos
  regionRadius_pos := a.regionRadius_pos
  region_interior := a.region_interior
  regions_disjoint := a.regions_disjoint
  placement := fun j ↦ BoundaryInsertion.Contract.placeFrom (a.placement j)
  placement_time := a.placement_time
  placement_chart := a.placement_chart
  ε := a.ε
  eps_admissible := a.eps_admissible
  eps_time := a.eps_time
  component := fun j ↦ BoundaryInsertion.Contract.solutionFrom (a.component j)
  component_pin := a.component_pin
  component_support := a.component_support
  component_force_support := a.component_force_support
  assembled_velocity := a.assembled_velocity
  assembled_velocity_formula := a.assembled_velocity_formula
  assembled_pressure := a.assembled_pressure
  assembled_pressure_formula := a.assembled_pressure_formula
  assembled_force := a.assembled_force
  assembled_force_formula := a.assembled_force_formula
  solution := BoundaryInsertion.Contract.solutionFrom a.solution
  solution_pin := a.solution_pin
  force_mem := a.force_mem
  rest := a.rest
  region_agreement := a.region_agreement
  region_blowup := a.region_blowup
  energy_bound := a.energy_bound
  dissipation_bound := a.dissipation_bound
  no_slip := a.no_slip

theorem to_of {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {Ω : Set Space} {hΩ : IsBoundedBoxOrSmoothDomain Ω}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : Contracts.V2.MultipleRegions.MultipleRegionsOmegaAPI P T Ω hΩ c r) :
    toContract (ofContract a) = a := rfl

theorem of_to {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {Ω : Set Space} {hΩ : IsBoundedBoxOrSmoothDomain Ω}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : NSFormalization.Section3.T24.MultipleRegionsOmegaAPI (ν := ν)
      P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T Ω hΩ c r) :
    ofContract (toContract a) = a := rfl

/-! ## Assembly from the registered packet projections -/

def regionsOmegaData {ν : ℝ} (P : PacketImportAPI ν)
    (Ω : Set Space) (hΩ : IsBoundedBoxOrSmoothDomain Ω) (T : ℝ) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N) (c : Fin N → Space) (r : Fin N → ℝ)
    (hr : ∀ j, 0 < r j)
    (hQ : ∀ j, closure (Metric.ball (c j) (r j)) ⊆ Ω)
    (hd : Pairwise (fun i j ↦
      Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))) :
    NSFormalization.Section3.T24.RegionsOmegaData ν P.velocity P.pressure P.force
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
  Ω := Ω
  hΩ := hΩ
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
def multipleRegionsOmega {ν : ℝ} (P : PacketImportAPI ν)
    (Ω : Set Space) (hΩ : IsBoundedBoxOrSmoothDomain Ω) (T : ℝ) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N) (c : Fin N → Space) (r : Fin N → ℝ)
    (hr : ∀ j, 0 < r j)
    (hQ : ∀ j, closure (Metric.ball (c j) (r j)) ⊆ Ω)
    (hd : Pairwise (fun i j ↦
      Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))) :
    Contracts.V2.MultipleRegions.MultipleRegionsOmegaAPI P T Ω hΩ c r :=
  toContract (NSFormalization.Section3.T24.multipleRegionsOmegaAPI
    (regionsOmegaData P Ω hΩ T hT N hN c r hr hQ hd))

/-- The registered packet-indexed existence statement. -/
theorem multipleRegionsOmegaStatement_holds : Contracts.V2.MultipleRegions.multipleRegionsOmegaStatement := by
  intro _ν _hν P Ω hΩ T hT N hN c r hr hQ hd
  exact ⟨multipleRegionsOmega P Ω hΩ T hT N hN c r hr hQ hd⟩

theorem multipleRegionsStatementV2_holds :
    Contracts.V2.MultipleRegions.multipleRegionsStatementV2 :=
  ⟨Bindings.multipleRegionsStatement_holds, multipleRegionsOmegaStatement_holds⟩

end BlowupDensity.Bindings.MultipleRegionsV2
