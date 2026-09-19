# REPORT_441 — T20 U12 `globalRegularity`

## 1. The theorem proved

Lane 441 proves `prop:critical` as the `CriticalRegularityTAPI.globalRegularity`
field verbatim at `c = criticalSmallnessH1`:

```lean
theorem globalRegularity : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤
```

The supporting theorem `maximal_squaredHTwoIntegralT_ne_top` proves T11's
exact local-finiteness premise for every `0 < S` satisfying
`ENNReal.ofReal S ≤ maximalLifespanT`.  It exhausts `(0,S)` by strict
subhorizons, applies U11's `continuationBound` on the classical solution
provided by `IsMaximalPeriodicSolution` at each subhorizon, and passes the
single finite U11 bound to the supremum.  The maximal-pair witness already
contains `w.velocity = u`, so `velocity_unique` is unnecessary.  The final
step is the proved, ball-free
`periodicContinuationH3API.lifespanInfiniteOfLocallyFinite`; no
`PeriodicRestartH1` hypothesis is used.

Both declarations depend on exactly
`[propext, Classical.choice, Quot.sound]`.  There is no named input and no
residual proposition.

## 2. Files delivered

- `formalization/NSFormalization/Section3/T20/GlobalRegularity.lean` — endpoint
  local-finiteness bridge and the canonical theorem.
- `research/T20/probes/global_regularity_closes.lean` — literal field-type
  match and a zero-force witness proving admissibility,
  `criticalRho 0 = 0 < criticalSmallnessH1 * 1`, and infinite lifespan.
- `research/T20/axioms_u12.lean` — transitive axiom audit for both declarations.
- `research/T20/ATTEMPTS_U12.md` — all failed compile approaches with exact
  diagnostics.
- `research/T20/T20_SPLIT.md` — U12 marked DONE with the actual endpoint route.
- `logs/LESSONS.md` — lane-specific maximal-pair/pin lesson.
- `research/T20/REPORT_441.md` — this report.

No existing Lean module was edited.

## 3. Gaps and exact errors

There is no remaining mathematical or Lean gap.  The six failed rounds are
recorded in full in `ATTEMPTS_U12.md`.  The proof-relevant diagnostics were:

```text
Type mismatch: add_le_add_right (Nat.cast_le.mpr hij) 2
has type 2 + ↑i ≤ 2 + ↑j
but is expected to have type ↑i + 2 ≤ ↑j + 2

Application type mismatch: hc.right.left has type
meanModeCriterionIntegral ... ≤ ...
but is expected to have type meanModeCriterionIntegral ... = ?m.680

error(lean.unknownIdentifier): Unknown identifier `mul_le_mul_right'`
```

The remaining diagnostics were the expected missing `.olean` before the first
module build and an omitted selective namespace import in the probe; both are
also copied exactly in the attempts file.

## 4. Commands and results

All Lake commands ran from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6` on builds.

- `lake build NSFormalization.Section3.T20.Continuation NSFormalization.Section3.T11.Assembly`
  — exit 0; dependency closure built successfully (`10655` jobs).
- `lake env lean ../formalization/NSFormalization/Section3/T20/GlobalRegularity.lean`
  — exit 0, zero output.
- `lake build NSFormalization.Section3.T20.GlobalRegularity`
  — exit 0; build completed successfully (`10656` jobs; only replayed upstream
  warnings).
- `lake env lean ../research/T20/probes/global_regularity_closes.lean`
  — exit 0, zero output.
- `lake env lean ../research/T20/axioms_u12.lean`
  — exit 0; both declarations print exactly
  `[propext, Classical.choice, Quot.sound]`.
- forbidden-token and heartbeat scans over the new proof module — no hits.
- `git diff --check` — exit 0.
- `make check` — exit 0; contract-policy tests and work-queue checks passed.
