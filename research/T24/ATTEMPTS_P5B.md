# Lane 500: P5.3 and P5.4

## Scope and interface

Only `MultipleOmegaRegions.lean` is introduced. P5.1/P5.2 constructors remain
with lane 497. Theorems take component velocity functions and the exact global
support/pin facts; the assembly supplies `fun j => (component j).velocity`.
The sum is definitionally `finiteVelocitySum`.

## P5.3

Agreement uses `Finset.sum_eq_single` and pairwise disjoint balls. Raw
`speed_unbounded_at_target` applied to `zeroPastField_speed` gives witnesses.
A witness has positive speed; the threaded global component support puts it
inside its ball directly. No periodization or spatial chart is used.
Initial compile exposed Lean section-variable omission (`Unknown identifier
component_support`); explicitly including the proof variables fixes it.

## Authorized existing-file edits

- `formalization/blueprint/entrypoints.json`: register the new proof module.
- `research/T24/T24_SPLIT.md`: unit status entries (at completion).
