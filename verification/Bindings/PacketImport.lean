import Contracts.V1.PacketImport
import Bindings.Packet
import NSFormalization.Section3.T14.PacketEnergy

/-! Binding for the T14 packet import and `eq:packetenergy` contract.

The selected packet is exactly the registered `Bindings.packet`; the two
energy fields are supplied by the canonical T14 theorems and transported
through the `l2Sq`/`dissipation` bridges from `Bindings.Packet`.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open BlowupDensity.Contracts.V1

/-! ## Definitional drift guard -/

theorem accumulatedForce_eq :
    Contracts.V1.accumulatedForce = NSFormalization.Section3.T14.accumulatedForce := rfl

/-! ## The proved packet-import API -/

def packetImportFamily : Contracts.V1.PacketImportFamily where
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
        { energy_le_work := by
            simpa only [BlowupDensity.Bindings.l2Sq_eq,
              BlowupDensity.Bindings.dissipation_eq, accumulatedForce_eq] using he
          work_eq_square := by
            simpa only [BlowupDensity.Bindings.l2Sq_eq, accumulatedForce_eq] using hw } }

theorem packetImport : Contracts.V1.packetImportStatement := by
  intro ν hν
  exact ⟨packetImportFamily.select ν hν⟩

end BlowupDensity.Bindings
