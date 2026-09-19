# T15 U14 attempts and exact residual

## Delivered branch

`Section3/T15/Convergence.lean` proves the entire `q = 1` specialization of
the canonical convergence field. This includes `0 ≤ s < 1/2` by squeezing
U13's packet bound and every `s < 0` by contraction under the actual
Fourier order-lowering map.

## Order-lowering elaboration failures

The first direct proof of order monotonicity unfolded the reweighting norm
estimate inside the nested infimum and timed out:

```text
../research/T15/probes/convergence_work.lean:15:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

Raising the permitted per-declaration budget did not repair that proof shape:

```text
../formalization/NSFormalization/Section3/T15/Convergence.lean:34:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
```

The final proof factors out `persistenceDown_norm_le_one`, changes that goal
definitionally to `torusOrderDown`, and applies the existing theorem
`T11.HighOrder.torusOrderDown_norm_le`. The completed declaration uses the
allowed, commented 400000-heartbeat local budget.

## The `q = 2` sign obstruction

The proposed route requires the assertion `0 < alphaT 2 2`. The direct Lean
arithmetic probe

```lean
example : 0 < alphaT 2 2 := by
  norm_num [alphaT]
```

fails exactly with:

```text
/tmp/q2_arithmetic_458.lean:3:28: error: unsolved goals
⊢ False
```

Indeed, the registered definition gives

```text
alphaT 2 2 = -3 + 3/2 + 1 = -1/2,
```

not `+1/2`. Thus `packetMixedScaling` makes the order-zero comparison scale
as `ε ^ (-1/2)`. The proved monotonicity

```lean
forceSobolevENormT 2 s F ≤ forceSobolevENormT 2 0 F
```

is true, but its right-hand side does not tend to zero and therefore cannot
establish the requested negative-order convergence.

The source tree contains the appropriate whole-space negative-order limits
`compact_scalar_force_L2_tendsto` and `compact_vector_force_L2_tendsto` in
`Source/CompactForceConvergence.lean`. Exhaustive searches found no torus
periodization estimate transferring those limits while preserving their
negative-order scaling. `Paper1/PeriodicNonpositiveForce.lean` only compares
periodic negative order through an order-zero quantity, which is insufficient
for `q = 2`.

## Exact canonical mismatch and residual

Trying to close the literal full canonical field by the completed theorem,

```lean
exact forceConvergence_one hf hc place
```

produces:

```text
/tmp/full_exact_458.lean:14:2: error: Type mismatch
  forceConvergence_one hf hc place
has type
  ∀ s < criticalOrder (ENNReal.toReal 1),
    Tendsto (fun ε => forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0)
but is expected to have type
  ∀ (q : ℝ≥0∞),
    q = 1 ∨ q = 2 →
      ∀ s < criticalOrder q.toReal,
        Tendsto (fun ε => forceSobolevENormT q s (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0)
```

The exact unproved residual is:

```lean
∀ s : ℝ, s < criticalOrder ((2 : ℝ≥0∞).toReal) →
  Tendsto
    (fun ε : ℝ ↦ forceSobolevENormT 2 s
      (periodizedScaledForce f place.x₀ place.T ε))
    (𝓝[>] 0) (𝓝 0)
```

Closing it requires a torus negative-order periodization estimate that reaches
the existing whole-space `L²_t H^s_x` concentration result without passing
through `H^0`. No named input or placeholder for that missing theorem has been
introduced.
