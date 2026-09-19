import NSFormalization.Section3.T24.MultipleRegions

/-! Final assembly of `prop:multiple` (`03-torus.tex:697-722`). -/
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
def multipleRegionsAPI {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} {M D : ℝ} (d : RegionsData ν u p f K M D) :
    MultipleRegionsAPI (ν := ν) u p f K M D d.T d.regionCenter d.regionRadius where
  T_pos := d.hT
  N_pos := d.N_pos
  regionRadius_pos := d.regionRadius_pos
  region_interior := d.region_interior
  regions_disjoint := d.regions_disjoint
  placement := d.placement
  placement_time := d.placement_time
  placement_chart := d.placement_chart
  scaling := d.scaling
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
  region_agreement := d.region_agreement
  region_blowup := d.region_blowup
  energy_bound := d.energy_bound
  dissipation_bound := d.dissipation_bound

/-- The raw universal existence statement of `prop:multiple`. -/
theorem multipleRegionsStatement_holds : multipleRegionsStatement := by
  intro ν _hν u p f K M D τ
    _velocity_smooth _pressure_smooth force_smooth force_support carrier_compact
    velocity_support pressure_support zero_initial_velocity _divergence_free
    _navier_stokes speed_unbounded square_integrable energy_isLUB
    dissipation_integrable dissipation_eq _quiet_pos _quiet_lt_one _force_quiet
    _velocity_quiet _pressure_quiet force_zero_nonpos velocity_extension_smooth
    pressure_extension_smooth extension_navier_stokes extension_divergence_free
    _energy_le_work _work_eq_square T hT N hN regionCenter regionRadius hr hQ hd
  let d : RegionsData ν u p f K M D :=
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
      T := T
      hT := hT
      N := N
      N_pos := hN
      regionCenter := regionCenter
      regionRadius := regionRadius
      regionRadius_pos := hr
      region_interior := hQ
      regions_disjoint := hd }
  exact ⟨multipleRegionsAPI d⟩

end NSFormalization.Section3.T24
