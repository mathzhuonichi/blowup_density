import Tests.PacketImport

/-!
# `T01.packet_import` conformance and transitive-axiom audit

Run from `verification/` with
`lake env lean ../research/T14/axioms_contract.lean`.
Every proof declaration below is expected to use only
`[propext, Classical.choice, Quot.sound]`.
-/

open BlowupDensity.Bindings

#print axioms BlowupDensity.Bindings.accumulatedForce_eq
#print axioms BlowupDensity.Bindings.packetImportFamily
#print axioms BlowupDensity.Bindings.packetImport
#print axioms BlowupDensity.Tests.checkedPacketImport

/-! The checked statement is the registered declaration and is built from the
concrete selected family, rather than assumed as a proposition parameter. -/
example : BlowupDensity.Contracts.V1.packetImportStatement :=
  BlowupDensity.Tests.checkedPacketImport

example (ν : ℝ) (hν : 0 < ν) :
    (BlowupDensity.Bindings.packetImportFamily.select ν hν).velocity =
      (BlowupDensity.Bindings.packet ν hν).velocity := rfl
