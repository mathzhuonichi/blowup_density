# Lane 486 attempts

Prerequisite closure build passed (10087 jobs). No failed proof attempts yet.
Skeleton checkpoint only; no theorem completion claimed.

## A1: slice support inference
The first interior proof inferred spacetime support from an unannotated function.
Exact diagnostic:
```text
InteriorBlowup.lean:53:31: error: Application type mismatch: The argument
  hx
has type
  (t, x) ∈ tsupport (scaledVelocity U place.x₀ place.T ε)
but is expected to have type
  ?m.386 ∈ tsupport fun x => scaledVelocity U place.x₀ place.T ε (t, x)
in the application
  hsupport t ht hx
```
Fix: explicitly pass the spatial slice to `subset_tsupport`. Commit 837962b3
was an intermediate checkpoint before this diagnostic was inspected; its commit
title overstates that checkpoint. The following commit verifies the correction.

## A2: neighborhood measure and set membership
```text
InteriorBlowup.lean:68:4: error(lean.unknownIdentifier): Unknown identifier `measure_pos_of_mem_nhds`
InteriorBlowup.lean:71:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ¬?m.108 < ?m.109
in the target expression
  y ∈ {y | ¬‖z y‖ₑ < ENNReal.ofReal M}
```
Fix: use `Measure.measure_pos_of_mem_nhds`; expose membership with `change`.
