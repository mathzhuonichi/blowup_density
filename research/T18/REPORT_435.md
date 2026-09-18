# REPORT 435

## Theorems

Added `diffSupportRadius` and `diffSupportRadius_pos` in `Section3/T18/Support.lean`.

## Files

Added Support.lean, `probes/u7_closes.lean`, `axioms_u7.lean`, and `ATTEMPTS_U7.md`.

## Gaps

`velocityDifference_support` requires a packet-support bridge absent from `ScalingAPI`; `diffSupport_in_chart` requires the specified carrier radius `R_K`, absent from `PlacementData`. Lean errors identify the remaining type/goal failures.

## Commands/results

`lake build NSFormalization.Section3.T18.Insertion` passes. `Support` does not compile because the two missing API facts leave unsolved goals.
