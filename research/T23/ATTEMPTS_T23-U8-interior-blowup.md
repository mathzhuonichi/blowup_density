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

## A3: conjunction projection after rewriting min
```text
Lifespan.lean:53:48: error: Tactic `assumption` failed
ht : t ∈ Ioo 0 T
⊢ t < T
```
Fix: `rw [min_eq_left hTSr.le]; exact ht.2`; `rwa` does not extract the conjunction.

## A4: section variables used only in proof
```text
InteriorBlowup.lean:131:30: error(lean.unknownIdentifier): Unknown identifier `D`
InteriorBlowup.lean:131:32: error(lean.unknownIdentifier): Unknown identifier `hspeed`
InteriorBlowup.lean:131:57: error(lean.unknownIdentifier): Unknown identifier `hscale`
InteriorBlowup.lean:131:65: error(lean.unknownIdentifier): Unknown identifier `hball`
InteriorBlowup.lean:132:5: error(lean.unknownIdentifier): Unknown identifier `hformula`
InteriorBlowup.lean:132:18: error(lean.unknownIdentifier): Unknown identifier `hsupport`
InteriorBlowup.lean:132:34: error(lean.unknownIdentifier): Unknown identifier `hcancel`
InteriorBlowup.lean:129:35: error: unsolved goals
⊢ ∀ (M : ℝ), 0 < M → ∀ (d : ℝ), 0 < d → ∃ t x,
  t ∈ Ioo 0 place.T ∧ place.T - d < t ∧
  x ∈ Metric.ball place.chartCenter place.chartRadius ∧ x ∈ Ω ∧ M < ‖velocity ε (t, x)‖
```
Fix: explicitly `include` the six proof-side hypotheses.
