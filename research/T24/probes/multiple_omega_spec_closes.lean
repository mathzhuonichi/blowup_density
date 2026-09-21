import NSFormalization.Section3.T24.MultipleOmega

/-! Type probes only, not an inhabitant of the multiple-region specification.
Every retained field is checked against its explicit type; shared torus fields
are checked separately against the same type expression with the torus record.
The last example specializes Ω to (0,1)^3 and N to one. -/
noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T24
open NSFormalization.Section3.T23
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ENNReal BigOperators
variable {ν T M D : ℝ} {u f : VelocityField} {p : PressureField}
  {K Ω : Set Space} {hΩ : IsBoundedBoxOrSmoothDomain Ω}
  {N : ℕ} {c : Fin N → Space} {r : Fin N → ℝ}
  (a : MultipleRegionsOmegaAPI (ν := ν) u p f K M D T Ω hΩ c r)
  (b : MultipleRegionsAPI (ν := ν) u p f K M D T c r)

-- T_pos: domain field type
example : 0 < T := a.T_pos

-- T_pos: shared torus type
example : 0 < T := b.T_pos

-- N_pos: domain field type
example : 0 < N := a.N_pos

-- N_pos: shared torus type
example : 0 < N := b.N_pos

-- regionRadius_pos: domain field type
example : ∀ j : Fin N, 0 < r j := a.regionRadius_pos

-- regionRadius_pos: shared torus type
example : ∀ j : Fin N, 0 < r j := b.regionRadius_pos

-- region_interior: domain field type
example : ∀ j : Fin N,
    closure (Metric.ball (c j) (r j)) ⊆ Ω := a.region_interior

-- regions_disjoint: domain field type
example : Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (c i) (r i))
      (Metric.ball (c j) (r j))) := a.regions_disjoint

-- regions_disjoint: shared torus type
example : Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (c i) (r i))
      (Metric.ball (c j) (r j))) := b.regions_disjoint

-- placement: domain field type
example : Fin N → DomainPlacementData u p f K := a.placement

-- placement_time: domain field type
example : ∀ j : Fin N, (a.placement j).T = T := a.placement_time

-- placement_time: shared torus type
example : ∀ j : Fin N, (b.placement j).T = T := b.placement_time

-- placement_chart: domain field type
example : ∀ j : Fin N,
    (a.placement j).chartCenter = c j ∧
      (a.placement j).chartRadius = r j := a.placement_chart

-- placement_chart: shared torus type
example : ∀ j : Fin N,
    (b.placement j).chartCenter = c j ∧
      (b.placement j).chartRadius = r j := b.placement_chart

-- ε: domain field type
example : Fin N → ℝ := a.ε

-- ε: shared torus type
example : Fin N → ℝ := b.ε

-- eps_admissible: domain field type
example : ∀ j : Fin N, a.ε j ∈ Ioc (0 : ℝ) (a.placement j).ε₀ := a.eps_admissible

-- eps_admissible: shared torus type
example : ∀ j : Fin N, b.ε j ∈ Ioc (0 : ℝ) (b.placement j).ε₀ := b.eps_admissible

-- eps_time: domain field type
example : ∀ j : Fin N, a.ε j ^ 2 < T := a.eps_time

-- eps_time: shared torus type
example : ∀ j : Fin N, b.ε j ^ 2 < T := b.eps_time

-- component: domain field type
example : ∀ j : Fin N,
    ClassicalSolutionOmega ν Ω (0 : SpatialField)
      (scaledForce f (a.placement j).x₀ T (a.ε j)) T := a.component

-- component_pin: domain field type
example : ∀ j : Fin N,
    (a.component j).velocity = scaledVelocity u (a.placement j).x₀ T (a.ε j) ∧
      (a.component j).pressure = domainNormalizePressure Ω (scaledPressure p (a.placement j).x₀ T (a.ε j)) := a.component_pin

-- component_support: domain field type
example : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    x ∉ Metric.ball (c j) (r j) →
      (a.component j).velocity (t, x) = 0 := a.component_support

-- component_force_support: domain field type
example : ∀ j : Fin N, ∀ t : ℝ, ∀ x : Space,
    x ∉ Metric.ball (c j) (r j) →
      scaledForce f (a.placement j).x₀ T (a.ε j) (t, x) = 0 := a.component_force_support

-- assembled_velocity: domain field type
example : SpaceTimeField := a.assembled_velocity

-- assembled_velocity: shared torus type
example : SpaceTimeField := b.assembled_velocity

-- assembled_pressure: domain field type
example : SpaceTimeScalar := a.assembled_pressure

-- assembled_pressure: shared torus type
example : SpaceTimeScalar := b.assembled_pressure

-- assembled_force: domain field type
example : SpaceTimeField := a.assembled_force

-- assembled_force: shared torus type
example : SpaceTimeField := b.assembled_force

-- solution: domain field type
example : ClassicalSolutionOmega ν Ω (0 : SpatialField) a.assembled_force T := a.solution

-- force_mem: domain field type
example : a.assembled_force ∈ forceClassOmega Ω := a.force_mem

-- rest: domain field type
example : ∀ x : Space, a.assembled_velocity (0, x) = 0 := a.rest

-- rest: shared torus type
example : ∀ x : Space, b.assembled_velocity (0, x) = 0 := b.rest

-- region_agreement: domain field type
example : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (c j) (r j),
      a.assembled_velocity (t, x) = (a.component j).velocity (t, x) := a.region_agreement

-- region_agreement: shared torus type
example : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (c j) (r j),
      b.assembled_velocity (t, x) = (b.component j).velocity (t, x) := b.region_agreement

-- region_blowup: domain field type
example : ∀ j : Fin N,
    SpeedUnboundedAtOn T (Metric.ball (c j) (r j))
      a.assembled_velocity := a.region_blowup

-- region_blowup: shared torus type
example : ∀ j : Fin N,
    SpeedUnboundedAtOn T (Metric.ball (c j) (r j))
      b.assembled_velocity := b.region_blowup

-- energy_bound: domain field type
example : (energyEssSupOmega Ω T a.assembled_velocity) ^ (2 : ℕ) ≤
    ENNReal.ofReal (M ^ 2 * ∑ j : Fin N, a.ε j) := a.energy_bound

-- dissipation_bound: domain field type
example : (energyGradientOmega Ω T a.assembled_velocity) ^ (2 : ℕ) =
    ENNReal.ofReal (D ^ 2 * ∑ j : Fin N, a.ε j) := a.dissipation_bound

-- no_slip: domain field type
example : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ frontier Ω, a.assembled_velocity (t, x) = 0 := a.no_slip

def unitBox : Set Space := {x | ∀ i : Fin 3, 0 < x i ∧ x i < 1}
def oneCenter : Fin 1 → Space := fun _ ↦ (1 / 2 : ℝ) • (WithLp.toLp 2 (fun _ : Fin 3 ↦ (1 : ℝ)))
def oneRadius : Fin 1 → ℝ := fun _ ↦ 1 / 4

-- Geometry and API inhabitation are not assumed to have been proved by this probe.
example (hbox : IsBoundedBoxOrSmoothDomain unitBox)
    (a : MultipleRegionsOmegaAPI (ν := ν) u p f K M D T
      unitBox hbox oneCenter oneRadius) :
    SpeedUnboundedAtOn T (Metric.ball (oneCenter 0) (oneRadius 0))
      a.assembled_velocity := a.region_blowup 0
