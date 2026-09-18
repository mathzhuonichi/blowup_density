# T11/U15 maximality attempts (lane 323)

## Successful route

1. Used `toFlow` for the easy inequality
   `maximalLifespanT ν a f ≤ PeriodicLifespan.lifespan ν a f`.
2. For the reverse inequality, completed an arbitrary Paper 1 `Flow` after
   pressure normalization.  Slab `ContDiffOn` gives smooth periodic slices;
   the missing `ContinuousOn` Fourier datum path is obtained by identifying
   datum distance with the square root of `periodicIntegerEnergy` of the
   slice difference and applying the existing local cube-integral continuity
   theorem.  Smooth pressure gives the `MemLp` gradient field, and
   `integral_torusLift` identifies cube normalization with `PressureGaugeT`.
3. Applied unconditional
   `exists_maximal_periodic_solution_of_lifespan_pos` and upgraded each of its
   normalized horizon flows with `ofNormalizedFlow`.
4. Proved `maximal_unique` natively: a strict inequality below the T10
   supremum yields a realized horizon above `t`; its midpoint is still below
   the supremum, so `velocity_unique` and `pressure_unique` apply to the two
   horizon representatives.

## Failed intermediate forms (resolved)

- The first local spatial-derivative composition used a nonexistent method:

  ```text
  Invalid field `comp_hasFDerivWithinAt`: The environment does not contain
  `HasFDerivAtFilter.comp_hasFDerivWithinAt`
  ```

  This was replaced by `HasFDerivWithinAt.comp` with an explicit `MapsTo`
  proof and `univ_mem`.

- The first monolithic datum-path proof exhausted the permitted declaration
  budget:

  ```text
  (deterministic) timeout at `whnf`, maximum number of heartbeats (400000)
  has been reached
  ```

  Factoring the norm identity and energy continuity into separate proved
  lemmas removed the timeout; no declaration exceeds the 400000 cap.

- Opening both T10 and Paper 1 initially made the torus names ambiguous:

  ```text
  Ambiguous term `torusLift`
  Ambiguous term `periodicTorusMeasure`
  ```

  The completed proof fully qualifies the T10 carrier and Paper 1 integral
  bridge at those sites.

## Single residual named input

U11 is not present on this branch.  The only retained input is exactly:

```lean
def PeriodicMaximalExistenceInput : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ T : ℝ, 0 < T ∧ Nonempty (ClassicalSolutionT ν a f T)
```

`maximalLifespanT_eq_lifespan` and `maximal_unique` are unconditional;
only `exists_maximal` consumes this input.  The probe instantiates its local
conclusion at a nonzero constant datum and a nonzero compact positive-time
bump force.
