import Contracts.V1.Scaling3

/-!
# Contract: finitely many prescribed singular regions

This is the reconciled T24b statement of `prop:multiple`
(`paper/sections/03-torus.tex:697-722`). It is restated over the registered
`PacketImportAPI`, `PlacementData`, `ScalingAPI`, and torus solution vocabulary.

The paper's bounded-domain / homogeneous-no-slip branch
(`03-torus.tex:698,706,720`) is deliberately outside this V1 contract. A
bounded-domain norm is registered, but no bounded-domain solution/no-slip
carrier is threaded through T24b; this contract states exactly the torus branch.
-/

noncomputable section
namespace BlowupDensity.Contracts.V1

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.Scaling3
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:710`: the finite superposition `u = ∑_j U_j`. -/
def finiteVelocitySum {N : ℕ} (U : Fin N → SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑ j : Fin N, U j z

/-- `03-torus.tex:710`: the finite superposition `p = ∑_j P_j`. -/
def finitePressureSum {N : ℕ} (P : Fin N → SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ∑ j : Fin N, P j z

/-- `03-torus.tex:710`: the finite superposition `f = ∑_j F_j`. -/
def finiteForceSum {N : ℕ} (F : Fin N → SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑ j : Fin N, F j z

/-- `03-torus.tex:713-717`: unbounded speed in a fixed spatial ball `B` in every
left neighbourhood of the terminal time `T`, i.e. the pointwise reading of
`limsup_{t↑T} ‖u(t)‖_{L∞(B)} = ∞`. -/
def SpeedUnboundedAtOn (T : ℝ) (B : Set Space) (u : SpaceTimeField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space,
      t ∈ Ioo (0 : ℝ) T ∧ T - δ < t ∧ x ∈ B ∧ M < ‖u (t, x)‖

/-- Proposition `prop:multiple` (`paper/sections/03-torus.tex:697-722`) on the
torus: at fixed `ν>0`, `T>0`, and `N` prescribed disjoint interior balls, a
forced solution from rest whose velocity blows up separately in each ball, with
finite energy and dissipation.

`Type`-valued: the record carries the per-region T15 placement/scaling data and
the selected component solutions. No new constant is introduced: `M, D` are the
imported packet's `energyBound`/`dissipationBound`.

The paper's bounded-domain / homogeneous-no-slip branch (`03-torus.tex:698,706,720`)
is deliberately omitted: the registered bounded-domain norm is not a
bounded-domain solution/no-slip carrier, so that branch remains out of V1 scope. -/
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
  placement : Fin N → Scaling3.PlacementData P.toPacketAPI
  placement_time : ∀ j : Fin N, (placement j).T = T
  placement_chart : ∀ j : Fin N,
    (placement j).chartCenter = regionCenter j ∧
      (placement j).chartRadius = regionRadius j
  scaling : ∀ j : Fin N, Scaling3.ScalingAPI P (placement j)
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

/-- `03-torus.tex:697-722`: the existence form of `prop:multiple`. For every
`ν>0`, imported packet, `T>0`, and every finite family of disjoint interior
balls, the multiple-regions API is inhabited. -/
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

end BlowupDensity.Contracts.V1
