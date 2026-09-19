# T23 U1 attempts

## A1 — unnecessary distance symmetry in the interior-margin proof

The first proof of `domainPlacementMargin_pos` rewrote `dist_comm` after
unfolding ball membership.  This reversed the already-correct orientation of
`Metric.mem_ball`.

Command:

```text
cd verification && lake env lean ../formalization/NSFormalization/Section3/T23/Placement.lean
```

Exact error:

```text
../formalization/NSFormalization/Section3/T23/Placement.lean:114:27: error: Application type mismatch: The argument
  hx₀
has type
  x₀ ∈ Metric.ball chartCenter chartRadius
but is expected to have type
  chartCenter ∈ Metric.ball x₀ chartRadius
in the application
  Metric.mem_ball.mp hx₀
```

Resolution: retain the `dist x₀ chartCenter` orientation produced directly by
`Metric.mem_ball`; no symmetry rewrite is needed.
