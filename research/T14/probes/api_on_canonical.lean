import Contracts.V1.Packet
import Bindings.Packet
import NSFormalization.Section3.T14.PacketEnergy

noncomputable section

namespace BlowupDensity.T14.Probe

open Set MeasureTheory
open BlowupDensity.Contracts.V1

def accumulatedForce (F : VelocityField) (t : ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) t, Real.sqrt (l2Sq F s)

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

def packetImportStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → Nonempty (PacketImportAPI ν)

structure PacketImportFamily where
  select : ∀ ν : ℝ, 0 < ν → PacketImportAPI ν

theorem accumulatedForce_eq_module (F : VelocityField) (t : ℝ) :
    accumulatedForce F t = NSFormalization.Section3.T14.accumulatedForce F t := rfl

theorem packetImport : packetImportStatement := by
  intro ν hν
  let P := BlowupDensity.Bindings.packet ν hν
  have he := NSFormalization.Section3.T14.energy_le_work_of_packet
    (ν := ν) (u := P.velocity) (f := P.force) (p := P.pressure)
    (K := P.carrier) hν P.carrier_compact P.velocity_smooth P.pressure_smooth
    P.force_smooth P.force_support P.velocity_support P.zero_initial_velocity
    P.divergence_free P.navier_stokes
  have hw := NSFormalization.Section3.T14.work_eq_square_of_packet
    P.force_smooth P.force_support
  refine ⟨{ toPacketAPI := P, energy := { energy_le_work := ?_, work_eq_square := ?_ } }⟩
  · simpa only [BlowupDensity.Bindings.l2Sq_eq,
      BlowupDensity.Bindings.dissipation_eq, accumulatedForce_eq_module] using he
  · simpa only [BlowupDensity.Bindings.l2Sq_eq,
      accumulatedForce_eq_module] using hw

def packetImportFamily : PacketImportFamily where
  select ν hν :=
    let P := BlowupDensity.Bindings.packet ν hν
    let he := NSFormalization.Section3.T14.energy_le_work_of_packet
      (ν := ν) (u := P.velocity) (f := P.force) (p := P.pressure)
      (K := P.carrier) hν P.carrier_compact P.velocity_smooth P.pressure_smooth
      P.force_smooth P.force_support P.velocity_support P.zero_initial_velocity
      P.divergence_free P.navier_stokes
    let hw := NSFormalization.Section3.T14.work_eq_square_of_packet
      P.force_smooth P.force_support
    { toPacketAPI := P
      energy :=
        { energy_le_work := by simpa only [BlowupDensity.Bindings.l2Sq_eq,
            BlowupDensity.Bindings.dissipation_eq, accumulatedForce_eq_module] using he
          work_eq_square := by simpa only [BlowupDensity.Bindings.l2Sq_eq,
            accumulatedForce_eq_module] using hw } }

example (ν : ℝ) (hν : 0 < ν) :
    (packetImportFamily.select ν hν).velocity =
      (BlowupDensity.Bindings.packet ν hν).velocity := by
  rfl

#print axioms accumulatedForce_eq_module
#print axioms packetImport
#print axioms packetImportFamily

end BlowupDensity.T14.Probe
