import NSFormalization.Section3.T24.MultipleOmegaAssembled
noncomputable section
namespace P5aProbe
open NSFormalization.Section3.T24
open NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Source.PacketScaling (zeroPastField)
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff Topology

variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsOmegaData ν u p f K M E)

theorem placement_time : ∀ j, (d.placement j).T = d.T := by
  exact d.placement_time

theorem placement_chart : ∀ j,
    (d.placement j).chartCenter = d.regionCenter j ∧
    (d.placement j).chartRadius = d.regionRadius j := by
  exact d.placement_chart

theorem eps_admissible : ∀ j, d.ε j ∈ Ioc (0 : ℝ) (d.placement j).ε₀ := by
  exact d.eps_admissible

theorem eps_time : ∀ j, d.ε j ^ 2 < d.T := by
  exact d.eps_time

theorem component_pin : ∀ j,
    (d.component j).velocity = scaledVelocity u (d.placement j).x₀ d.T (d.ε j) ∧
    (d.component j).pressure = domainNormalizePressure d.Ω (scaledPressure p (d.placement j).x₀ d.T (d.ε j)) := by
  exact d.component_pin

theorem component_support : ∀ j, ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x : Space,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) → (d.component j).velocity (t, x) = 0 := by
  exact d.component_support

theorem component_force_support : ∀ j, ∀ t : ℝ, ∀ x : Space,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) →
      scaledForce f (d.placement j).x₀ d.T (d.ε j) (t, x) = 0 := by
  exact d.component_force_support


theorem T_pos : 0 < d.T := by exact d.hT
theorem N_pos : 0 < d.N := by exact d.N_pos
theorem regionRadius_pos : ∀ j, 0 < d.regionRadius j := by exact d.regionRadius_pos
theorem region_interior : ∀ j,
    closure (Metric.ball (d.regionCenter j) (d.regionRadius j)) ⊆ d.Ω := by
  exact d.region_interior
theorem regions_disjoint : Pairwise (fun i j : Fin d.N =>
    Disjoint (Metric.ball (d.regionCenter i) (d.regionRadius i))
      (Metric.ball (d.regionCenter j) (d.regionRadius j))) := by
  exact d.regions_disjoint
example : Fin d.N → DomainPlacementData u p f K := by exact d.placement
example : Fin d.N → ℝ := by exact d.ε
example : ∀ j : Fin d.N, ClassicalSolutionOmega ν d.Ω (0 : SpatialField)
    (scaledForce f (d.placement j).x₀ d.T (d.ε j)) d.T := by
  exact d.component
example : SpaceTime → Space := by exact d.assembledVelocity
example : SpaceTime → ℝ := by exact d.assembledPressure
example : SpaceTime → Space := by exact d.assembledForce
example : ClassicalSolutionOmega ν d.Ω (0 : SpatialField) d.assembledForce d.T := by
  exact d.solution

theorem assembled_velocity_formula :
    d.assembledVelocity = finiteVelocitySum (fun j => (d.component j).velocity) := by
  exact d.assembled_velocity_formula

theorem assembled_pressure_formula :
    d.assembledPressure = finitePressureSum (fun j => (d.component j).pressure) := by
  exact d.assembled_pressure_formula

theorem assembled_force_formula : d.assembledForce =
    finiteForceSum (fun j => scaledForce f (d.placement j).x₀ d.T (d.ε j)) := by
  exact d.assembled_force_formula

theorem solution_pin : d.solution.velocity = d.assembledVelocity ∧
    d.solution.pressure = d.assembledPressure := by
  exact d.solution_pin

theorem force_mem : d.assembledForce ∈ forceClassOmega d.Ω := by
  exact d.force_mem

theorem rest : ∀ x : Space, d.assembledVelocity (0, x) = 0 := by
  exact d.rest

theorem no_slip : ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x ∈ frontier d.Ω,
    d.assembledVelocity (t, x) = 0 := by
  exact d.no_slip

end P5aProbe
