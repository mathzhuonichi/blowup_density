# Lane 363 report — T15 U-TB2 Parseval-at-zero bridge

## 1. Theorem proved

The lane proves the stronger bridge
`periodicSobolevENorm_zero_eq_of_memLp`: if `z` is spatially periodic and
`torusLift z` is in `L²(T³)`, then
`periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure`.
The requested smooth statement `periodicSobolevENorm_zero_eq` follows by
deriving the `MemLp` hypothesis from `ContDiff ℝ ∞`.  The companion theorem
`periodicSobolevENorm_zero_ne_top` records finiteness for smooth periodic
fields.

## 2. Lean contents

`formalization/NSFormalization/Section3/T15/ParsevalZero.lean` packages
`parseval_backward`, the explicit `iInf` collapse using `datum_unique`, and
`parseval_forward`.  The smooth `MemLp` helper is proved componentwise from
`Paper1.memLp_torusLift`.  The non-vacuity probe
`research/T15/probes/parseval_zero_closes.lean` defines the nonzero constant
mode `coordinateVector 0`, proves it smooth and periodic, and instantiates the
bridge identity.  `research/T15/axioms_utb2.lean` audits all three public
theorems.

## 3. Remaining gaps

No U-TB2 proof gap remains.  The stronger theorem still assumes the natural
periodicity and physical `MemLp` hypotheses; these are exactly what
`parseval_backward` requires.  The broader T15 units (including U-TB1 and the
scaling assembly) remain outside this lane.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.ParsevalZero` — passed.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T15/ParsevalZero.lean` — passed.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/parseval_zero_closes.lean` — passed.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T15/axioms_utb2.lean` — passed; each audited declaration prints exactly `[propext, Classical.choice, Quot.sound]`.
