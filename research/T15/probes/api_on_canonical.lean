import Contracts.V1.Packet
import Contracts.V1.TorusData
import Contracts.V1.Scaling
import Bindings.Scaling
import NSFormalization.Section3.T14.PacketEnergy
import NSFormalization.Section3.T15.Bridges

/-!
# T15 U1 API conformance probe

This is the small contract-side check: the T15 definitions below are copied
from `research/T15/Spec.lean` and each is definitionally the corresponding
definition in the canonical module.  The final section also checks the
registered contract spellings through their upstream bindings.
-/

noncomputable section

namespace NSFormalization.Section3.T15.Probe

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Section3.T10
open NSFormalization.Section3.T14
open NSFormalization.Section3.T13
open NSFormalization.Section3.T15
open scoped ContDiff ENNReal BigOperators Topology

/-! The T14 packet import carrier used by the Spec's rescaling binders. -/

structure PacketEnergyAPI {ν : ℝ} (P : PacketAPI ν) : Prop where
  energy_le_work : ∀ t ∈ Ico (0 : ℝ) 1,
    l2Sq P.velocity t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation P.velocity s)
      ≤ 2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq P.force s) * accumulatedForce P.force s)
  work_eq_square : ∀ t ∈ Ico (0 : ℝ) 1,
    2 * (∫ s in Ioo (0 : ℝ) t,
      Real.sqrt (l2Sq P.force s) * accumulatedForce P.force s)
      = accumulatedForce P.force t ^ 2

structure PacketImportAPI (ν : ℝ) extends PacketAPI ν where
  energy : PacketEnergyAPI toPacketAPI

/-! Token-for-token T15 definitions, with only the namespace changed. -/

def scaledStartTime (T ε : ℝ) : ℝ := T - ε ^ 2

def scaledSourcePoint (x₀ : Space) (T ε : ℝ) (z : SpaceTime) : SpaceTime :=
  ((ε⁻¹) ^ 2 * (z.1 - scaledStartTime T ε), ε⁻¹ • (z.2 - x₀))

def scaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ ε⁻¹ • zeroPastField P.velocity (scaledSourcePoint x₀ T ε z)

def scaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeScalar :=
  fun z ↦ (ε⁻¹) ^ 2 *
    zeroPastField P.pressure (scaledSourcePoint x₀ T ε z)

def scaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ (ε⁻¹) ^ 3 • P.force (scaledSourcePoint x₀ T ε z)

def periodizedScaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledVelocity P x₀ T ε (z.1, x)) z.2

def periodizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  fun z ↦ ∑' n : PeriodicFrequency,
    scaledPressure P x₀ T ε (z.1, z.2 - latticeVector n)

def periodizedScaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledForce P x₀ T ε (z.1, x)) z.2

def normalizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  normalizePressureT (periodizedScaledPressure P x₀ T ε)

def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

theorem scaledStartTime_eq_module (T ε : ℝ) :
    scaledStartTime T ε = NSFormalization.Section3.T15.scaledStartTime T ε := rfl

theorem scaledSourcePoint_eq_module (x₀ : Space) (T ε : ℝ) (z : SpaceTime) :
    scaledSourcePoint x₀ T ε z =
      NSFormalization.Section3.T15.scaledSourcePoint x₀ T ε z := rfl

theorem scaledVelocity_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    scaledVelocity P x₀ T ε =
      NSFormalization.Section3.T15.scaledVelocity P.velocity x₀ T ε := rfl

theorem scaledPressure_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    scaledPressure P x₀ T ε =
      NSFormalization.Section3.T15.scaledPressure P.pressure x₀ T ε := rfl

theorem scaledForce_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    scaledForce P x₀ T ε =
      NSFormalization.Section3.T15.scaledForce P.force x₀ T ε := rfl

theorem periodizedScaledVelocity_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    periodizedScaledVelocity P x₀ T ε =
      NSFormalization.Section3.T15.periodizedScaledVelocity P.velocity x₀ T ε := rfl

theorem periodizedScaledPressure_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    periodizedScaledPressure P x₀ T ε =
      NSFormalization.Section3.T15.periodizedScaledPressure P.pressure x₀ T ε := rfl

theorem periodizedScaledForce_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    periodizedScaledForce P x₀ T ε =
      NSFormalization.Section3.T15.periodizedScaledForce P.force x₀ T ε := rfl

theorem normalizedScaledPressure_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    normalizedScaledPressure P x₀ T ε =
      NSFormalization.Section3.T15.normalizedScaledPressure P.pressure x₀ T ε := rfl

theorem alphaT_eq_module (p q : ℝ≥0∞) :
    alphaT p q = NSFormalization.Section3.T15.alphaT p q := rfl

/-! Contract spellings, checked through the upstream objects named by the
bindings. -/

theorem contract_scaledPacket_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.Contracts.V1.scaledPacket P.velocity x₀ T ε =
      NSFormalization.Section3.T15.scaledVelocity P.velocity x₀ T ε := rfl

theorem contract_scaledPressure_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.Contracts.V1.scaledPressure P.pressure x₀ T ε =
      NSFormalization.Section3.T15.scaledPressure P.pressure x₀ T ε := rfl

theorem contract_scaledForce_eq_module {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) :
    BlowupDensity.Contracts.V1.scaledForce P.force x₀ T ε =
      NSFormalization.Section3.T15.scaledForce P.force x₀ T ε := rfl

theorem contract_alpha_eq_module (p q : ℝ≥0∞) :
    BlowupDensity.Contracts.V1.alpha p q =
      NSFormalization.Section3.T15.alphaT p q := rfl

theorem contract_completedDense_eq_module (q : ℝ≥0∞) (s : ℝ)
    (S : Set BlowupDensity.Contracts.V1.Data.SpaceTimeField) :
    BlowupDensity.Contracts.V1.Data.CompletedDense q s S =
      NSFormalization.Section4.B01.CompletedDense q s S := rfl

theorem contract_completedDenseHomogeneous_eq_module (q : ℝ≥0∞) (s : ℝ)
    (S : Set BlowupDensity.Contracts.V1.Data.SpaceTimeField) :
    BlowupDensity.Contracts.V1.Data.CompletedDenseHomogeneous q s S =
      NSFormalization.Section3.T15.completedDenseHomogeneous q s S := rfl

end NSFormalization.Section3.T15.Probe
