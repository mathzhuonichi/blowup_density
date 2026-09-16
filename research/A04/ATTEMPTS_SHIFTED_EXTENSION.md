# Lane 217 — shifted classical extension

## Result

`shiftedLocalExtension : ShiftedLocalExtension` discharges lane 215's exact
remaining input. There is no replacement hypothesis. The constructive core is
`exists_shifted_glue`: given ν>0, an actual solution w on `[0,T)`, an interior
restart b∈[0,T), an actual restarted solution w₂ on `[0,L)`, and T<b+L, it
produces `Nonempty (ClassicalSolutionR ν a f (b+L))`.

The original definition of `ShiftedLocalExtension` and every existing Lean
module are unchanged. Three new consumers discharge the extension binder:
`restartBeyond_of_memForceR'`, `extendsBeyond_of_memForceR'`, and
`lifespanInfiniteOfLocallyFinite_of_memForceR'`. The first fixes f and S
before choosing δ and uses the existing H⁷ bound. This does not establish
lane 215's rejected cross-force/H¹ quantifier order.

## Overlap identity and pressure construction

The uniqueness theorem used is **A02.velocity_unique_core**, from
`Section4/A02/Uniqueness.lean`. It is the classical finite-energy/bounded
uniqueness theorem; the proof does not directly invoke lane 188's
`A01.quadratic_mild_unique`. Apply it to `shiftedSolution w b hb` and w₂ at
time t−b to obtain w(t,x)=w₂(t−b,x) on `[b,T)` when T<b+L.
A02's `patch` is not shifted gluing: it simply chooses the longer of two
solutions having the same original datum, force, and zero-time origin.

The task proposed a smooth cutoff blend of pressures. An existing stronger
API makes that unnecessary: normalize each pressure at the spatial basepoint
0, using **A02.ClassicalSolutionR.normalizePressure**. The resulting solutions
n and n₂ have the same velocities as w and w₂. Apply
**A02.pressure_gauge_core** to the shifted w and w₂, followed by
**A02.normalizePressure_gauge_invariant**. This gives the literal identity

```
n.pressure (t,x) = n₂.pressure (t-b,x),  b ≤ t < T.
```

Choose c=(b+T)/2. Define the glued velocity and pressure by the first normalized
solution for t<c and the translated second normalized solution for t≥c.
Both fields agree with their first chart on all `[0,T)` and with their second
chart on all `[b,b+L)`. Thus the seam is fake for pressure as well as velocity.
No function defined only on the overlap is extended across T. Each subtraction
p(t,x)−p(t,0) uses its own solution's pressure on its own interval. In particular,
near T only the second solution is used. The pressure need not retain w's
original gauge, which is not part of `ShiftedLocalExtension`'s conclusion.

## All fields of ClassicalSolutionR

- Positive horizon and initial velocity follow from the original solution and
  b<T. The first chart contains time zero, including when b=0.
- `contDiffOn_overlap` transfers joint smoothness from the two charts to the
  union by neighborhoods within the slab. It retains one-sided smoothness at 0.
- Divergence and pressure-gradient L² membership transfer through whole-slice
  equality. The pressure normalization API already proves gradient invariance.
- `residual_eq_of_local_slices` uses equality of all spatial slices on a time
  neighborhood. Spatial derivatives and advection then agree, and the ambient
  time Fréchet derivatives agree by `EventuallyEq.fderiv_eq`.
- `restarted_residual` uses the vector-valued chain rule with s↦s−b; its
  derivative is 1. The shifted force simplifies to f(t,x). This is used only
  at t>b, so momentum is never requested at restarted time zero.
- At every Sobolev order, `D01.isSobolevDatum_unique` identifies the two datum
  paths on the overlap. Paste them at the same c and use
  `continuousOn_overlap`; the resulting continuous path represents exactly
  the glued velocity at every time in `[0,b+L)`.

Finally split T<b+L versus b+L≤T. In the first case apply
`A02.horizon_le_lifespan` to the constructed solution. In the second,
monotonicity of `ENNReal.ofReal` and the original w suffice.

## Attempts and elaboration fixes

The initially considered cutoff route is mathematically valid but requires
extra scalar cutoff and gradient algebra. Reading Restrict and Maximal revealed
the existing normalization API, which removes that additional construction.
An attempt to use `patch` directly would have mismatched datum/force indices;
no such application is part of the delivered proof.

The first Lean checks exposed routine elaboration issues:

- `simp only [spatialDerivative, hs]` at a function equality reported
  `simp made no progress`; first introduce the spatial point with `funext`.
- A bare `Eventually.mono` expression did not elaborate field notation for
  `.fderiv_eq`; give the intermediate equality its explicit `=ᶠ[𝓝 t]` type.
- The translated residual requires explicit translated `v` and `q` arguments
  in `residual_eq_of_local_slices` so higher-order unification sees the chart.
- Normalized solution lets must be explicitly unfolded when simplifying their
  projected fields against the original solution's fields.
- `linarith` does not reduce `(id - fun _ => b) t`; `dsimp` exposes t−b.

All were resolved without heartbeat changes or additional assumptions.
The conformance file audits every one of the 12 production declarations and
instantiates actual `A04.zeroSol` inputs in the gluing branch and the lifespan
and integral-continuation theorems. There is no named input to test for
nonzero satisfiability: the construction applies to arbitrary actual nonzero
solutions with precisely the same hypotheses as the target.

Gate results are recorded in `REPORT_217.md`; raw logs stay in worktree-local
`tmp/`.
