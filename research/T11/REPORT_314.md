# Lane 314 report — T11/U4 viscosity rescaling

## 1. Theorems with exact statements

```lean
theorem scaled_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        unitViscosityInitialT ν a ∈ initialClassT ∧
          unitViscosityForceT ν f ∈ forceClassT
```

```lean
theorem inverse_identities : ∀ (ν : ℝ), 0 < ν →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar) (f : SpaceTimeField),
      restoreViscosityVelocityT ν (unitViscosityVelocityT ν u) = u ∧
        restoreViscosityPressureT ν (unitViscosityPressureT ν p) = p ∧
        restoreViscosityForceT ν (unitViscosityForceT ν f) = f
```

The force proof transports its compact positive-time support from `K` to the
compact image `(fun t ↦ ν * t) '' K`.  No instance declaration was added.

## 2. Files

- `formalization/NSFormalization/Section3/T11/Rescaling.lean` — the two exact
  U4 theorems and private class-preservation helpers.
- `research/T11/probes/rescaling_closes.lean` — verbatim target closure checks
  and a non-vacuity example with a genuinely nonzero periodic datum.
- `research/T11/axioms_rescaling.lean` — guarded transitive-axiom checks for
  both exported declarations.
- `research/T11/ATTEMPTS_RESCALING.md` — declaration search, proof route,
  intermediate exact errors, and the named-input record.
- `research/T11/T11_SPLIT.md` — appended U4 completion status.

## 3. Gaps with error text

No proof gap and no named input remain.  The two intermediate failures were
`Unknown identifier spatialDivergence_const_smul` and the unsolved equality
`((fun x => ν) * id) (z.1 / ν) = z.1`; their full contexts and fixes are
recorded in `ATTEMPTS_RESCALING.md`.

Both public declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Rescaling`
  — passed, 0 errors.
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/Rescaling.lean`
  — passed, 0 errors.
- `cd verification && lake env lean ../research/T11/probes/rescaling_closes.lean`
  — passed, 0 errors; both exact target shapes close and the non-vacuity
  witness elaborates.
- `cd verification && lake env lean ../research/T11/axioms_rescaling.lean`
  — passed; both guarded declarations have exactly the standard three axioms.
- `make check` from the worktree root — passed.
