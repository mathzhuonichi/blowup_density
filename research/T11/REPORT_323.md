# Lane 323 report — T11/U15 maximal solutions

## 1. Proved theorems

The module proves the exact maximal-existence field, conditional only on the
single U11 existence input:

```lean
theorem exists_maximal (H : PeriodicMaximalExistenceInput) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u p
```

It proves the exact uniqueness field unconditionally:

```lean
theorem maximal_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u₁ p₁ →
          IsMaximalPeriodicSolution ν a f u₂ p₂ →
            ∀ t : ℝ, 0 ≤ t →
              ENNReal.ofReal t < maximalLifespanT ν a f →
                ∀ x : Space,
                  u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x)
```

The two lifespan notions are now identified without hypotheses:

```lean
theorem maximalLifespanT_eq_lifespan (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) :
    maximalLifespanT ν a f =
      NSFormalization.Paper1.PeriodicLifespan.lifespan ν a f
```

## 2. Lean files and supporting results

- `formalization/NSFormalization/Section3/T11/Maximal.lean` contains the
  Flow-to-classical upgrade, both lifespan inequalities, maximal gluing, and
  presingular uniqueness.
- `research/T11/probes/maximal_closes.lean` checks the two API fields verbatim,
  checks lifespan equality, and gives the nonzero datum/nonzero compact-force
  input probe.
- `research/T11/axioms_maximal.lean` guards every new declaration at exactly
  `[propext, Classical.choice, Quot.sound]`.
- `research/T11/ATTEMPTS_MAXIMAL.md` records the route, resolved elaboration
  failures, and the residual input verbatim.

The important supporting result is `ofNormalizedFlow`: joint slab smoothness
produces continuous integer-order Fourier datum paths, smooth pressure gives
the torus `L²` gradient, and cube normalization gives the Haar gauge.  Thus
`flowToClassical` makes the reverse lifespan inequality genuine rather than
assuming equality of the two solution structures.

## 3. Remaining gap

U11 has not landed, so `exists_maximal` takes exactly one named input,
`PeriodicMaximalExistenceInput`, asserting a positive-horizon
`ClassicalSolutionT` for every positive viscosity, admissible datum, and force
in `forceClassT`.  There is no other conditional result in this lane.

Resolved error text and the exact input are recorded in
`ATTEMPTS_MAXIMAL.md`.  In particular, the earlier 400000-heartbeat timeout was
removed by factoring the datum-path proof; it is not a remaining build error.

## 4. Verification

All required gates passed with zero errors:

```text
cd verification
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Maximal
lake env lean ../formalization/NSFormalization/Section3/T11/Maximal.lean
lake env lean ../research/T11/probes/maximal_closes.lean
lake env lean ../research/T11/axioms_maximal.lean
cd ..
make check
```

The build emitted only pre-existing upstream warnings.  The axiom audit
confirmed that all 16 new declarations print exactly
`[propext, Classical.choice, Quot.sound]`.
