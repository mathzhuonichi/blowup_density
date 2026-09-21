import NSFormalization.Section3.T24.MultipleOmegaAssembled
import NSFormalization.Section3.T24.MultipleOmegaRegions

/-! Proposition 3.16, `paper/revised/sections/03-torus.tex:511–535`:
"Fix finitely many disjoint interior balls"; "In a bounded domain its boundary
condition is homogeneous no-slip." "On B_j the velocity equals U_j, proving
the stated separate limsup for each ball." Assembly from un-periodised packets. -/
noncomputable section
namespace NSFormalization.Section3.T24

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Source.PacketScaling (zeroPastField)
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff Topology

/-- Assemble all thirty canonical fields from the region data and the Ub1--Ub6
constructions. -/
def multipleRegionsOmegaAPI {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} {M D : ℝ} (d : RegionsOmegaData ν u p f K M D) :
    MultipleRegionsOmegaAPI (ν := ν) u p f K M D d.T d.Ω d.hΩ d.regionCenter d.regionRadius where
  T_pos := d.hT
  N_pos := d.N_pos
  regionRadius_pos := d.regionRadius_pos
  region_interior := d.region_interior
  regions_disjoint := d.regions_disjoint
  placement := d.placement
  placement_time := d.placement_time
  placement_chart := d.placement_chart
  ε := d.ε
  eps_admissible := d.eps_admissible
  eps_time := d.eps_time
  component := d.component
  component_pin := d.component_pin
  component_support := d.component_support
  component_force_support := d.component_force_support
  assembled_velocity := d.assembledVelocity
  assembled_velocity_formula := d.assembled_velocity_formula
  assembled_pressure := d.assembledPressure
  assembled_pressure_formula := d.assembled_pressure_formula
  assembled_force := d.assembledForce
  assembled_force_formula := d.assembled_force_formula
  solution := d.solution
  solution_pin := d.solution_pin
  force_mem := d.force_mem
  rest := d.rest
  region_agreement := OmegaRegions.region_agreement d.regions_disjoint d.component_support
  region_blowup := OmegaRegions.region_blowup d.regions_disjoint d.component_support
    (fun j => (d.component_pin j).1) (fun j => (d.eps_admissible j).1) d.eps_time d.blowup
  energy_bound := OmegaRegions.energy_bound d.regions_disjoint d.component_support
    d.placement d.packet d.eps_admissible (fun j => (d.component_pin j).1) d.region_interior
  dissipation_bound := OmegaRegions.dissipation_bound d.regions_disjoint d.placement d.packet
    d.placement_time d.placement_chart d.eps_admissible
    (fun j => (d.component_pin j).1) d.region_interior
  no_slip := d.no_slip

/-- The raw universal existence statement of `prop:multiple`. -/
theorem multipleRegionsOmegaStatement_holds : multipleRegionsOmegaStatement := by
  intro ν _hν u p f K M D τ
    _velocity_smooth _pressure_smooth force_smooth force_support carrier_compact
    velocity_support pressure_support zero_initial_velocity _divergence_free
    _navier_stokes speed_unbounded square_integrable energy_isLUB
    dissipation_integrable dissipation_eq _quiet_pos _quiet_lt_one _force_quiet
    _velocity_quiet _pressure_quiet force_zero_nonpos velocity_extension_smooth
    pressure_extension_smooth extension_navier_stokes extension_divergence_free
    _energy_le_work _work_eq_square Ω hΩ T hT N hN regionCenter regionRadius hr hQ hd
  let d : RegionsOmegaData ν u p f K M D :=
    { packet :=
        { extension_smooth := velocity_extension_smooth
          carrier_compact := carrier_compact
          support := velocity_support
          square_int := square_integrable
          zero_initial := zero_initial_velocity
          energy_isLUB := energy_isLUB
          dissipation_int := dissipation_integrable
          dissipation_eq := dissipation_eq }
      pressure_support := pressure_support
      pressure_smooth := pressure_extension_smooth
      force_smooth := force_smooth
      force_support := force_support
      force_zero := force_zero_nonpos
      momentum := extension_navier_stokes
      divergence := extension_divergence_free
      blowup := speed_unbounded
      Ω := Ω
      hΩ := hΩ
      T := T
      hT := hT
      N := N
      N_pos := hN
      regionCenter := regionCenter
      regionRadius := regionRadius
      regionRadius_pos := hr
      region_interior := hQ
      regions_disjoint := hd }
  exact ⟨multipleRegionsOmegaAPI d⟩

end NSFormalization.Section3.T24
