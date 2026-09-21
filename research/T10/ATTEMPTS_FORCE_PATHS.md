# Lane 312 attempts

All commands source `scripts/lean-env.sh`; Lake runs from `verification/`
with `LEAN_NUM_THREADS=6`. No new instances or heartbeat overrides are used.

## Successful routes

- Construct smooth real vector data from Paper1's scalar weighted `lp`
  representatives; use Fourier conjugate reflection to enter the real subspace.
  The amended integrability conjunct follows from vector `MemLp` on the cube.
- For continuity at `t₀`, subtract the represented slice at `t₀`. Each scalar
  coefficient norm is the square root of the integer energy of
  `f(t,·) − f(t₀,·)`. Paper1's continuous integer energy gives norm convergence
  to zero, without differentiation under the integral.
- Compact temporal support transfers to coefficients, and continuous compactly
  supported paths are in every time `L^q`, including both requested endpoints.
- Sum scalar derivative Parseval over the nine entries of the Frobenius tensor.
  Construct the homogeneous datum using `sqrt(periodicAngularFrequencySq k)`;
  weighted summability ensures that no default-zero infinite sum is used.
- Removing the zero mode preserves angular energy. This gives the physical
  gradient/homogeneous norm equality and then the energy equality by a.e.
  congruence on the time interval, without time measurability assumptions.

## Resolved Lean errors (exact excerpts)

1. Running the source directly before building its dependency closure:

```text
error: object file '/data_8T/ping/blowup_density/.claude/worktrees/312-T10-force-paths/formalization/.lake/build/lib/lean/NSFormalization/Section3/T10/FourierCalculus.olean' of module NSFormalization.Section3.T10.FourierCalculus does not exist
```

Built the new target from `verification/` first.

2. Inferred composition spellings obstructed rewriting under implicit transparency:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖Paper1.smoothPeriodicWeightedFourierLp ?s ?f ?hf ?hp‖
```

Gave the component smoothness and energy continuity facts explicit lambda types.

3. Incorrect continuity unfolding lemma:

```text
Unknown identifier `continuousAt_iff`
```

Used `change Filter.Tendsto _ _ _` and unfolded `ContinuousAt` only at the
last norm-convergence step.

4. General strong measurability instance search tried a complex structure on
   the real submodule:

```text
failed to synthesize
  Module ℂ ↥(PeriodicSobolev ↑m)
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
```

Used `Continuous.stronglyMeasurable_of_hasCompactSupport` with the already
proved support fact. No extra instance and no heartbeat increase was needed.

5. Square-root conversion required explicit reciprocal normalization:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?x ^ (1 / 2)
```

Normalized `2⁻¹ = 1 / 2`. For equality to a square root used `sq_eq_sq₀` and
`Real.sq_sqrt`; the guessed name below does not exist:

```text
Unknown constant `Real.eq_sqrt`
```

6. The homogeneous datum uses complex scalar multiplication, whereas the
   constructor uses real scalar multiplication. Simplifying the norm directly
   resolves the apparent mismatch:

```text
‖(↑A).ofLp i‖ ^ 2 =
  ∑' (i_1 : PeriodicFrequency),
    ‖↑√(periodicAngularFrequencySq i_1) • periodicFourierCoeff (fun x => ↑((v x).ofLp i)) i_1‖ ^ 2
```

7. Projection of the vector Laplacian finite sum:

```text
Unknown constant `PiLp.sum_apply`
```

Used `WithLp.ofLp_sum` followed by `Finset.sum_apply`.

8. Non-vacuity example elaboration:

```text
Tactic `apply` failed: could not unify the conclusion of `memForceT_time_smul ...`
  MemForceT fun z => ↑profile z.1 • ?m.3 z.2
with the goal
  MemForceT force
```

Unfolded the example force and supplied its spatial profile explicitly.

No unresolved errors or named mathematical inputs remain. The coefficient
path is proved continuous, not `ContDiff`; the task explicitly permits this
regularity. The broader COMPARISON item 12 inhomogeneous intersection norm
comparison remains separate from the requested physical/coefficient identities.
