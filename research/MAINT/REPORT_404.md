# Lane 404 — remove T16 `if_pos` / `if_neg` deprecations

## 1. What changed

Only the three deprecated proof steps in `physicalCorrection_cancels` were changed.  The pinned
signatures were checked first: `ite_eq_left hc` proves `(if c then t else e) = t`, and
`ite_eq_right hnc` proves `(if c then t else e) = e`.

Exact before/after lines in `formalization/NSFormalization/Section3/T16/Assembly.lean`:

```text
327: exact if_neg h                  -> exact ite_eq_right h
332: rwa [if_pos hsT] at hy'        -> rwa [ite_eq_left hsT] at hy'
362: exact (if_pos ht.2).symm       -> exact (ite_eq_left ht.2).symm
```

No statement, declaration, hypothesis, rewrite direction, or surrounding proof structure changed.

## 2. Files

- `formalization/NSFormalization/Section3/T16/Assembly.lean`: the three authorized proof-line
  replacements above, and nothing else.
- `research/MAINT/REPORT_404.md`: this maintenance record.

No other file under `formalization/` was changed.  No file under `Paper1/`, `Source/`, or Section 4
was changed.

## 3. Residual warnings

`LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T16/Assembly.lean`
exited 0 and printed nothing: the three target deprecation warnings are gone and the module itself
is warning-free.

The downstream `lake build` succeeded but replayed 14 pre-existing, out-of-scope dependency
warnings from seven untouched files: `Source/FiniteHilbertBochner.lean` (3),
`Source/RealSobolev.lean` (3), `Paper3/SpatiallyCompactTime.lean` (1),
`Paper3/RealPositiveDensity.lean` (4), `Paper3/RealVectorPositiveDensity.lean` (1),
`Source/PacketForceExtension.lean` (1), and `Source/ViscosityPacket.lean` (1).  The only replayed
`if_pos` deprecation was `Source/PacketForceExtension.lean:44:25`, which is expressly out of this
lane's scope.  There are no residual warnings from `Section3/T16/Assembly.lean`,
`Section3/T17/Transport.lean`, or `Bindings/LocalPotential.lean`.

## 4. Commands and results

All Lake commands were run from `verification/` after `. scripts/lean-env.sh` with
`LEAN_NUM_THREADS=6`.

- Pinned replacement check via `lake env lean /dev/stdin` with `#check` / `#print` for
  `ite_eq_left` and `ite_eq_right`: exit 0; signatures matched the replacements above.
- `lake env lean ../formalization/NSFormalization/Section3/T16/Assembly.lean`: exit 0, exactly zero
  output.
- `grep -rln "Section3.T16.Assembly" formalization verification`: run as requested; in addition to
  cached build artifacts it found the two source importers.  The source-only confirmation found
  `formalization/NSFormalization/Section3/T17/Transport.lean` and
  `verification/Bindings/LocalPotential.lean`.
- `lake build NSFormalization.Section3.T17.Transport Bindings.LocalPotential`: exit 0,
  `Build completed successfully (9369 jobs)`; both importers and the changed assembly rebuilt.
- `#print axioms` for `physicalCorrection_cancels`, `localPotentialAPI`, and `localPotential`:
  each printed exactly `[propext, Classical.choice, Quot.sound]`.
- From the worktree root,
  `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh`: exit 0,
  `gates OK`; `make check` passed (13 policy tests, 45 work items consistent), all 42 contract tests
  passed with standard logical axioms only, and `make test-mutations` rejected both mutations as
  required.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`: exit 0;
  `registered_contracts: 42`, `base_compatibility_checked: true`.
- `git diff --check`: exit 0.

