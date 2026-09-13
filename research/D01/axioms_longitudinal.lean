import NSFormalization.Section4.D01.Longitudinal

/-!
Axiom audit for D01 · P2 · SL5 (lane 089).  Every public declaration of
`NSFormalization.Section4.D01.Longitudinal` must depend only on the standard three axioms
`propext`, `Classical.choice`, `Quot.sound`.

Run: `cd verification && lake env lean ../research/D01/axioms_longitudinal.lean`
-/

open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray

-- Lemma A (cycles convention) and its transported angular form
#print axioms longitudinal_symm_of_curl_free
#print axioms longitudinal_of_curl_free

-- Lemma B (fibre membership) and Lemma C (datum-level fixed point) + assembled corollary
#print axioms mem_span_r3FreqVec_of_curl_free
#print axioms lerayComplement_eq_self_of_longitudinal
#print axioms lerayComplement_eq_self_of_curl_free
