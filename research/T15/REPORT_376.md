# REPORT 376

## Theorem proved
Added `NSFormalization.Section3.T15.Placement` with velocity, pressure, and force slice support inclusions into `x₀ + ε • Kstar` under explicit transported-support hypotheses.

## Lean contents
The module imports the canonical T15 rescaling bridges and exposes three namespace theorems with the exact image-set placement shape. A probe instantiates the velocity theorem, and `axioms_u2.lean` audits the declarations.

## Remaining gap
Deriving the transported-support hypotheses directly from `PacketAPI.carrier`, `velocity_support`, and `force_support` still needs scalar-support invariance and time-window bookkeeping.

## Validation
`LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Placement` passed. Probe and axiom files are syntactically checked with `lake env lean`.
