import Contracts.V1.Scaling3
import Bindings.Scaling3
import TestSupport.Axioms

noncomputable section
namespace BlowupDensity.Tests
open Set MeasureTheory Filter Topology
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal

/-- Full statement for every selected packet family and every shared placement. -/
theorem checkedScaling3 : Scaling3.scalingStatement :=
  Bindings.Scaling3.scalingStatement_holds

run_cmd TestSupport.checkAxioms ``checkedScaling3

section Conformance
variable {ν : ℝ} (P : PacketImportAPI ν) (place : Scaling3.PlacementData P.toPacketAPI)

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∃ S : ClassicalSolutionT ν (0 : SpatialField)
        (Scaling3.periodizedScaledForce P place.x₀ place.T ε) place.T,
      S.velocity = Scaling3.periodizedScaledVelocity P place.x₀ place.T ε ∧
        S.pressure = Scaling3.normalizedScaledPressure P place.x₀ place.T ε :=
  (Bindings.Scaling3.scalingAPI P place).solution

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyEssSupT place.T (Scaling3.periodizedScaledVelocity P place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.energyBound) :=
  (Bindings.Scaling3.scalingAPI P place).packetEnergyIdentity

example : ∀ (q : ℝ≥0∞), (q = 1 ∨ q = 2) → ∀ s : ℝ,
    s < criticalOrder q.toReal →
      Tendsto (fun ε : ℝ ↦ forceSobolevENormT q s
        (Scaling3.periodizedScaledForce P place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0) :=
  (Bindings.Scaling3.scalingAPI P place).forceConvergence
end Conformance

/-- A full API at the registered packet, with any prescribed positive horizon. -/
def checkedScaling3Packet (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    Scaling3.ScalingAPI (Bindings.packetImportFamily.select ν hν)
      (Bindings.Scaling3.placementData (Bindings.packet ν hν) T hT) :=
  Bindings.Scaling3.scalingPacket ν hν T hT

run_cmd TestSupport.checkAxioms ``checkedScaling3Packet

example (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    (Bindings.Scaling3.placementData (Bindings.packet ν hν) T hT).T = T := rfl

/-- The registered source packet has a nonzero velocity before blowup. -/
theorem scaling3_source_nonzero (ν : ℝ) (hν : 0 < ν) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x, (Bindings.packet ν hν).velocity (t, x) ≠ 0 := by
  obtain ⟨t, x, ht, _, hx⟩ := (Bindings.packet ν hν).speed_unbounded
    1 (by norm_num) 1 (by norm_num)
  refine ⟨t, ht, x, ?_⟩
  intro hz
  rw [hz, norm_zero] at hx
  linarith

/-- The assembled torus velocity is nonzero at an admissible positive scale. -/
theorem scaling3_periodized_nonzero (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    let P := Bindings.packetImportFamily.select ν hν
    let place := Bindings.Scaling3.placementData (Bindings.packet ν hν) T hT
    ∃ ε ∈ Ioc (0 : ℝ) place.ε₀, ∃ t ∈ Ioo (0 : ℝ) T, ∃ x,
      Scaling3.periodizedScaledVelocity P place.x₀ T ε (t, x) ≠ 0 := by
  dsimp only
  let place := Bindings.Scaling3.placementData (Bindings.packet ν hν) T hT
  have hε : place.ε₀ ∈ Ioc (0 : ℝ) place.ε₀ := ⟨place.eps_pos, le_rfl⟩
  obtain ⟨t, x, ht, _, hx⟩ := (checkedScaling3Packet ν hν T hT).unboundedSpeed
    place.ε₀ hε 1 (by norm_num) 1 (by norm_num)
  refine ⟨place.ε₀, hε, t, ht, x, ?_⟩
  change 1 < ‖Scaling3.periodizedScaledVelocity (Bindings.packetImportFamily.select ν hν)
    place.x₀ T place.ε₀ (t, x)‖ at hx
  intro hz
  rw [hz, norm_zero] at hx
  linarith

run_cmd TestSupport.checkAxioms ``scaling3_source_nonzero
run_cmd TestSupport.checkAxioms ``scaling3_periodized_nonzero
end BlowupDensity.Tests
