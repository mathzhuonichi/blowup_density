import Bindings.Scaling3
import NSFormalization.Section3.T24.MultipleComponents

/-! Synchronized Spec block: only the formerly draft dependencies now resolve
through their registered T10/T13/T14/T15 namespaces. Both conversions check
all 30 fields; the projection examples below independently check their types. -/
noncomputable section
namespace BlowupDensity.T24.Multiple
open Set MeasureTheory
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData Contracts.V1.TorusLocalTheory
open Contracts.V1.Scaling3
open scoped ContDiff ENNReal BigOperators Topology

def finiteVelocitySum {N : ℕ} (U : Fin N → SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑ j : Fin N, U j z


def finitePressureSum {N : ℕ} (P : Fin N → SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ∑ j : Fin N, P j z


def finiteForceSum {N : ℕ} (F : Fin N → SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑ j : Fin N, F j z


def SpeedUnboundedAtOn (T : ℝ) (B : Set Space) (u : SpaceTimeField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space,
      t ∈ Ioo (0 : ℝ) T ∧ T - δ < t ∧ x ∈ B ∧ M < ‖u (t, x)‖


structure MultipleRegionsAPI {ν : ℝ} (P : PacketImportAPI ν) (T : ℝ)
    {N : ℕ} (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ) : Type where

  T_pos : 0 < T

  N_pos : 0 < N

  regionRadius_pos : ∀ j : Fin N, 0 < regionRadius j

  region_interior : ∀ j : Fin N,
    closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆ interior fundamentalCube

  regions_disjoint : Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (regionCenter i) (regionRadius i))
      (Metric.ball (regionCenter j) (regionRadius j)))

  placement : Fin N → PlacementData P.toPacketAPI

  placement_time : ∀ j : Fin N, (placement j).T = T

  placement_chart : ∀ j : Fin N,
    (placement j).chartCenter = regionCenter j ∧
      (placement j).chartRadius = regionRadius j

  scaling : ∀ j : Fin N, ScalingAPI P (placement j)

  ε : Fin N → ℝ

  eps_admissible : ∀ j : Fin N, ε j ∈ Ioc (0 : ℝ) (placement j).ε₀

  eps_time : ∀ j : Fin N, ε j ^ 2 < T

  component : ∀ j : Fin N,
    ClassicalSolutionT ν (0 : SpatialField)
      (periodizedScaledForce P (placement j).x₀ T (ε j)) T

  component_pin : ∀ j : Fin N,
    (component j).velocity = periodizedScaledVelocity P (placement j).x₀ T (ε j) ∧
      (component j).pressure = normalizedScaledPressure P (placement j).x₀ T (ε j)

  component_support : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) →
      (component j).velocity (t, x) = 0

  component_force_support : ∀ j : Fin N, ∀ t : ℝ, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) →
      periodizedScaledForce P (placement j).x₀ T (ε j) (t, x) = 0

  assembled_velocity : SpaceTimeField

  assembled_velocity_formula :
    assembled_velocity = finiteVelocitySum (fun j ↦ (component j).velocity)

  assembled_pressure : SpaceTimeScalar

  assembled_pressure_formula :
    assembled_pressure = finitePressureSum (fun j ↦ (component j).pressure)

  assembled_force : SpaceTimeField

  assembled_force_formula :
    assembled_force =
      finiteForceSum (fun j ↦ periodizedScaledForce P (placement j).x₀ T (ε j))

  solution : ClassicalSolutionT ν (0 : SpatialField) assembled_force T

  solution_pin :
    solution.velocity = assembled_velocity ∧ solution.pressure = assembled_pressure

  force_mem : assembled_force ∈ forceClassT

  rest : ∀ x : Space, assembled_velocity (0, x) = 0

  region_agreement : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (regionCenter j) (regionRadius j),
      assembled_velocity (t, x) = (component j).velocity (t, x)

  region_blowup : ∀ j : Fin N,
    SpeedUnboundedAtOn T (Metric.ball (regionCenter j) (regionRadius j))
      assembled_velocity

  energy_bound : (energyEssSupT T assembled_velocity) ^ (2 : ℕ) ≤
    ENNReal.ofReal (P.energyBound ^ 2 * ∑ j : Fin N, ε j)

  dissipation_bound : (energyGradientT T assembled_velocity) ^ (2 : ℕ) =
    ENNReal.ofReal (P.dissipationBound ^ 2 * ∑ j : Fin N, ε j)


def multipleRegionsStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν) (T : ℝ), 0 < T →
    ∀ (N : ℕ), 0 < N →
      ∀ (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ),
        (∀ j : Fin N, 0 < regionRadius j) →
        (∀ j : Fin N, closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆
          interior fundamentalCube) →
        Pairwise (fun i j : Fin N ↦
          Disjoint (Metric.ball (regionCenter i) (regionRadius i))
            (Metric.ball (regionCenter j) (regionRadius j))) →
        Nonempty (MultipleRegionsAPI P T regionCenter regionRadius)

end BlowupDensity.T24.Multiple

namespace MultipleCanonicalProbe
open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.Scaling3
open BlowupDensity.T24.Multiple
open scoped ENNReal BigOperators Topology

variable {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
  {c : Fin N → Space} {r : Fin N → ℝ}

def ofSpec (a : MultipleRegionsAPI P T c r) : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r where
  T_pos := a.T_pos
  N_pos := a.N_pos
  regionRadius_pos := a.regionRadius_pos
  region_interior := a.region_interior
  regions_disjoint := a.regions_disjoint
  placement := fun j => BlowupDensity.Bindings.Scaling3.placementOfSpec (a.placement j)
  placement_time := a.placement_time
  placement_chart := a.placement_chart
  scaling := fun j => BlowupDensity.Bindings.Scaling3.scalingOfSpec (a.scaling j)
  ε := a.ε
  eps_admissible := a.eps_admissible
  eps_time := a.eps_time
  component := fun j => BlowupDensity.Bindings.TorusLocalTheory.ofContract (a.component j)
  component_pin := a.component_pin
  component_support := a.component_support
  component_force_support := a.component_force_support
  assembled_velocity := a.assembled_velocity
  assembled_velocity_formula := a.assembled_velocity_formula
  assembled_pressure := a.assembled_pressure
  assembled_pressure_formula := a.assembled_pressure_formula
  assembled_force := a.assembled_force
  assembled_force_formula := a.assembled_force_formula
  solution := BlowupDensity.Bindings.TorusLocalTheory.ofContract a.solution
  solution_pin := a.solution_pin
  force_mem := a.force_mem
  rest := a.rest
  region_agreement := a.region_agreement
  region_blowup := a.region_blowup
  energy_bound := a.energy_bound
  dissipation_bound := a.dissipation_bound

def toSpec (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) : MultipleRegionsAPI P T c r where
  T_pos := a.T_pos
  N_pos := a.N_pos
  regionRadius_pos := a.regionRadius_pos
  region_interior := a.region_interior
  regions_disjoint := a.regions_disjoint
  placement := fun j => BlowupDensity.Bindings.Scaling3.placementToSpec (a.placement j)
  placement_time := a.placement_time
  placement_chart := a.placement_chart
  scaling := fun j => BlowupDensity.Bindings.Scaling3.scalingToSpec (a.scaling j)
  ε := a.ε
  eps_admissible := a.eps_admissible
  eps_time := a.eps_time
  component := fun j => BlowupDensity.Bindings.TorusLocalTheory.toContract (a.component j)
  component_pin := a.component_pin
  component_support := a.component_support
  component_force_support := a.component_force_support
  assembled_velocity := a.assembled_velocity
  assembled_velocity_formula := a.assembled_velocity_formula
  assembled_pressure := a.assembled_pressure
  assembled_pressure_formula := a.assembled_pressure_formula
  assembled_force := a.assembled_force
  assembled_force_formula := a.assembled_force_formula
  solution := BlowupDensity.Bindings.TorusLocalTheory.toContract a.solution
  solution_pin := a.solution_pin
  force_mem := a.force_mem
  rest := a.rest
  region_agreement := a.region_agreement
  region_blowup := a.region_blowup
  energy_bound := a.energy_bound
  dissipation_bound := a.dissipation_bound

-- Spec projection: T_pos
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    0 < T := (toSpec a).T_pos

-- Spec projection: N_pos
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    0 < N := (toSpec a).N_pos

-- Spec projection: regionRadius_pos
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N, 0 < r j := (toSpec a).regionRadius_pos

-- Spec projection: region_interior
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N,
    closure (Metric.ball (c j) (r j)) ⊆ interior fundamentalCube := (toSpec a).region_interior

-- Spec projection: regions_disjoint
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (c i) (r i))
      (Metric.ball (c j) (r j))) := (toSpec a).regions_disjoint

-- Spec projection: placement
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    Fin N → PlacementData P.toPacketAPI := (toSpec a).placement

-- Spec projection: placement_time
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N, ((toSpec a).placement j).T = T := (toSpec a).placement_time

-- Spec projection: placement_chart
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N,
    ((toSpec a).placement j).chartCenter = c j ∧
      ((toSpec a).placement j).chartRadius = r j := (toSpec a).placement_chart

-- Spec projection: scaling
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N, ScalingAPI P ((toSpec a).placement j) := (toSpec a).scaling

-- Spec projection: ε
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    Fin N → ℝ := (toSpec a).ε

-- Spec projection: eps_admissible
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N, (toSpec a).ε j ∈ Ioc (0 : ℝ) ((toSpec a).placement j).ε₀ := (toSpec a).eps_admissible

-- Spec projection: eps_time
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N, (toSpec a).ε j ^ 2 < T := (toSpec a).eps_time

-- Spec projection: component
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N,
    ClassicalSolutionT ν (0 : SpatialField)
      (periodizedScaledForce P ((toSpec a).placement j).x₀ T ((toSpec a).ε j)) T := (toSpec a).component

-- Spec projection: component_pin
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N,
    ((toSpec a).component j).velocity = periodizedScaledVelocity P ((toSpec a).placement j).x₀ T ((toSpec a).ε j) ∧
      ((toSpec a).component j).pressure = normalizedScaledPressure P ((toSpec a).placement j).x₀ T ((toSpec a).ε j) := (toSpec a).component_pin

-- Spec projection: component_support
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (c j) (r j) →
      ((toSpec a).component j).velocity (t, x) = 0 := (toSpec a).component_support

-- Spec projection: component_force_support
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N, ∀ t : ℝ, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (c j) (r j) →
      periodizedScaledForce P ((toSpec a).placement j).x₀ T ((toSpec a).ε j) (t, x) = 0 := (toSpec a).component_force_support

-- Spec projection: assembled_velocity
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    SpaceTimeField := (toSpec a).assembled_velocity

-- Spec projection: assembled_velocity_formula
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    (toSpec a).assembled_velocity = finiteVelocitySum (fun j ↦ ((toSpec a).component j).velocity) := (toSpec a).assembled_velocity_formula

-- Spec projection: assembled_pressure
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    SpaceTimeScalar := (toSpec a).assembled_pressure

-- Spec projection: assembled_pressure_formula
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    (toSpec a).assembled_pressure = finitePressureSum (fun j ↦ ((toSpec a).component j).pressure) := (toSpec a).assembled_pressure_formula

-- Spec projection: assembled_force
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    SpaceTimeField := (toSpec a).assembled_force

-- Spec projection: assembled_force_formula
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    (toSpec a).assembled_force =
      finiteForceSum (fun j ↦ periodizedScaledForce P ((toSpec a).placement j).x₀ T ((toSpec a).ε j)) := (toSpec a).assembled_force_formula

-- Spec projection: solution
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ClassicalSolutionT ν (0 : SpatialField) (toSpec a).assembled_force T := (toSpec a).solution

-- Spec projection: solution_pin
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    (toSpec a).solution.velocity = (toSpec a).assembled_velocity ∧ (toSpec a).solution.pressure = (toSpec a).assembled_pressure := (toSpec a).solution_pin

-- Spec projection: force_mem
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    (toSpec a).assembled_force ∈ forceClassT := (toSpec a).force_mem

-- Spec projection: rest
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ x : Space, (toSpec a).assembled_velocity (0, x) = 0 := (toSpec a).rest

-- Spec projection: region_agreement
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (c j) (r j),
      (toSpec a).assembled_velocity (t, x) = ((toSpec a).component j).velocity (t, x) := (toSpec a).region_agreement

-- Spec projection: region_blowup
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    ∀ j : Fin N,
    SpeedUnboundedAtOn T (Metric.ball (c j) (r j))
      (toSpec a).assembled_velocity := (toSpec a).region_blowup

-- Spec projection: energy_bound
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    (energyEssSupT T (toSpec a).assembled_velocity) ^ (2 : ℕ) ≤
    ENNReal.ofReal (P.energyBound ^ 2 * ∑ j : Fin N, (toSpec a).ε j) := (toSpec a).energy_bound

-- Spec projection: dissipation_bound
example (a : NSFormalization.Section3.T24.MultipleRegionsAPI (ν := ν) P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound T c r) :
    (energyGradientT T (toSpec a).assembled_velocity) ^ (2 : ℕ) =
    ENNReal.ofReal (P.dissipationBound ^ 2 * ∑ j : Fin N, (toSpec a).ε j) := (toSpec a).dissipation_bound


/-- All raw hypotheses come from an arbitrary imported packet. -/
def regionsData (P : PacketImportAPI ν) (T : ℝ) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N) (c : Fin N → Space) (r : Fin N → ℝ)
    (hr : ∀ j, 0 < r j)
    (hQ : ∀ j, closure (Metric.ball (c j) (r j)) ⊆ interior fundamentalCube)
    (hd : Pairwise (fun i j => Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j)))) :
    NSFormalization.Section3.T24.RegionsData ν P.velocity P.pressure P.force
      P.carrier P.energyBound P.dissipationBound where
  packet := ⟨P.velocity_extension_smooth, P.carrier_compact, P.velocity_support,
    P.square_integrable, P.zero_initial_velocity, P.energy_isLUB,
    P.dissipation_integrable, P.dissipation_eq⟩
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

example : @BlowupDensity.T24.Multiple.finiteVelocitySum =
    @NSFormalization.Section3.T24.finiteVelocitySum := rfl
example : @BlowupDensity.T24.Multiple.finitePressureSum =
    @NSFormalization.Section3.T24.finitePressureSum := rfl
example : @BlowupDensity.T24.Multiple.finiteForceSum =
    @NSFormalization.Section3.T24.finiteForceSum := rfl
example : BlowupDensity.T24.Multiple.SpeedUnboundedAtOn =
    NSFormalization.Section3.T24.SpeedUnboundedAtOn := rfl

/-- The raw universal statement supplies the Spec quantifiers without a new premise. -/
example (h : NSFormalization.Section3.T24.multipleRegionsStatement) :
    BlowupDensity.T24.Multiple.multipleRegionsStatement := by
  intro ν hν P T hT N hN c r hr hQ hd
  exact (h ν hν P.velocity P.pressure P.force P.carrier
    P.energyBound P.dissipationBound P.quietTime
    P.velocity_smooth P.pressure_smooth P.force_smooth P.force_support
    P.carrier_compact P.velocity_support P.pressure_support P.zero_initial_velocity
    P.divergence_free P.navier_stokes P.speed_unbounded P.square_integrable
    P.energy_isLUB P.dissipation_integrable P.dissipation_eq
    P.quiet_pos P.quiet_lt_one P.force_quiet P.velocity_quiet P.pressure_quiet
    P.force_zero_nonpos P.velocity_extension_smooth P.pressure_extension_smooth
    P.extension_navier_stokes P.extension_divergence_free
    P.energy.energy_le_work P.energy.work_eq_square T hT N hN c r hr hQ hd).map toSpec

end MultipleCanonicalProbe
