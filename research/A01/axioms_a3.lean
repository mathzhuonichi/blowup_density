import NSFormalization.Section4.A01.Propagation

/-! Axiom audit for A01 unit A3 (lane 122).  Expected for every declaration:
`[propext, Classical.choice, Quot.sound]` — the standard three, no `sorryAx`,
no new axioms.  Check with `cd verification && lake env lean ../research/A01/axioms_a3.lean`. -/

open NSFormalization.Section4.A01

#print axioms gronwall_bddAbove_Ico
#print axioms higherOrder_bddAbove
#print axioms higherOrder_bddAbove_lowestOrderSq
#print axioms higherOrder_bddAbove_fixedDriverSq
