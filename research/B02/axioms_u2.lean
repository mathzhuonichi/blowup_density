/-
Conformance check for B02 unit 2 (`annularSchwartz`) — sub-lemmas SL1, SL2.

Unit 2 is not yet complete (SL3 reality + SL4 slice/homogeneous assembly remain;
see `research/B02/U2_SPLIT.md`), so there is no spec-field `example` yet.  This file
only audits the transitive axioms of the two sub-lemmas proved so far, plus the
reused right-inverse helper.  Every public declaration of
`NSFormalization.Section4.B02.AnnularSchwartz` must depend on exactly
`propext`, `Classical.choice`, `Quot.sound`.

Check with:
  cd verification && lake env lean ../research/B02/axioms_u2.lean
-/
import NSFormalization.Section4.B02.AnnularSchwartz

#print axioms NSFormalization.Section4.B02.contDiff_rpow_mul_of_annulus
#print axioms NSFormalization.Section4.B02.schwartzAngularDilation_dilationInv
#print axioms NSFormalization.Section4.B02.exists_schwartz_angularFourier_eq
