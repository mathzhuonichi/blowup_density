/-
Transitive-axiom audit for T24a unit Ua9 (lane 430): the canonical assembly of
`AffineVariationAPI` (`research/T24/Spec.lean:1010-1121`), its registered
contract `T04.affine_variation`, the binding and the acceptance test.

Run: `cd verification && lake env lean ../research/T24/axioms_ua9.lean`
Expected: every line prints `[propext, Classical.choice, Quot.sound]`.

`Tests.AffineVariation` additionally runs `TestSupport.checkAxioms` on the two
checked declarations at build time.
-/
import NSFormalization.Section3.T24.AffineAssembly
import Contracts.V1.AffineVariation
import Bindings.AffineVariation
import Tests.AffineVariation

open NSFormalization.Section3.T24

-- §1 the packet energy assembly (`‖U‖_{E_1} < ∞`, the clause `PacketAPI` lacks)
#print axioms energyEssSup_le_of_isLUB
#print axioms energyGradient_lt_top_of_dissipation
#print axioms energyENorm_lt_top_of_packet

-- §2 the canonical thirteen-field assembly
#print axioms affineVariationCanonical

-- §3 the binding: drift guards, raw-data extraction, the two API instances
#print axioms BlowupDensity.Bindings.affineCylinder_eq
#print axioms BlowupDensity.Bindings.affineAdmissible_eq
#print axioms BlowupDensity.Bindings.crossAdvection_eq
#print axioms BlowupDensity.Bindings.affineVelocity_eq
#print axioms BlowupDensity.Bindings.affinePressure_eq
#print axioms BlowupDensity.Bindings.affineForce_eq
#print axioms BlowupDensity.Bindings.ckSeminormE_eq
#print axioms BlowupDensity.Bindings.packetRawData
#print axioms BlowupDensity.Bindings.affineVariation
#print axioms BlowupDensity.Bindings.affineVariationPacket
#print axioms BlowupDensity.Bindings.affineVariationStatement_holds

-- §4 the acceptance test and its nonzero witness
#print axioms BlowupDensity.Tests.checkedAffineVariation
#print axioms BlowupDensity.Tests.checkedAffineVariationStatement
#print axioms BlowupDensity.Tests.affineTestWitness_admissible
#print axioms BlowupDensity.Tests.affineTestWitness_ne_zero
#print axioms BlowupDensity.Tests.affineTestZero_admissible
