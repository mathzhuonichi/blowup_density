# Lane 286-T10: vector Parseval

## 1. Theorems proved (exact canonical API statements)

Namespace: `NSFormalization.Section3.T10`.

```lean
theorem parseval_forward :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure

theorem parseval_backward :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      MemLp (torusLift z) 2 periodicTorusMeasure →
        ∃ A : PeriodicSobolev 0, IsPeriodicDatum 0 z A
```

Backward Parseval constructs the three scalar Fourier Hilbert-basis images,
proves their conjugate-reflection symmetry, and supplies integrability using
L² membership on probability Haar measure. Forward Parseval proves the real
squared-norm identity componentwise and converts it to the extended norm via
`Lp.enorm_toLp`. Normalization is exactly the canonical unit-torus measure.

## 2. Files and proof surface

Only five new files are delivered:

- `formalization/NSFormalization/Section3/T10/Parseval.lean`: both targets plus
  seven helpers: `periodicTorusMeasure_probability`, `memLp_torusLift_component`,
  `fourier_repr_toLp`, `periodicFourierCoeff_real_neg`, `norm_toLp_sq_integral`,
  `datum_component_norm_sq`, and `datum_norm_sq_integral`.
- `research/T10/probes/parseval_closes.lean`: exact-field closure examples;
  concrete zero-field non-vacuity; arbitrary constant-field existence with
  coefficient norm equal to the constant's Euclidean norm.
- `research/T10/axioms_parseval.lean`: audits all nine named theorems.
- `research/T10/ATTEMPTS_PARSEVAL.md`: search/proof routes and exact failed-run
  diagnostics with their resolutions.
- `research/T10/REPORT_286.md`: this report and handoff.

Every named theorem prints exactly `[propext, Classical.choice, Quot.sound]`.
There are no additional assumptions or heartbeat overrides. Existing modules,
including `PeriodicData.lean`, and existing records are untouched, as required
by the new-files-only rule. No push, merge, or rebase was performed.

## 3. Gaps and errors

No residual gap or named hypothesis. Both exact targets are proved.

Intermediate failures were elaboration/interface issues: explicit arguments to
`PiLp.continuous_apply`; unfolding aliases; rewriting `star` to `conj`;
`Lp.enorm_toLp` namespace; the actual lemma name `ofReal_norm`; and explicit
constant/exponent normalization in the probe. Full exact diagnostics and fixes
are in `ATTEMPTS_PARSEVAL.md`. All are resolved.

The final direct Lean runs have no warnings or errors. Lake build replays
pre-existing warnings from imported modules; the new module has none.

## 4. Commands and results

All Lean commands source `. scripts/lean-env.sh` and set `LEAN_NUM_THREADS=6`.
Direct Lake commands run from `verification/`.

| Command | Result |
| --- | --- |
| `lake build NSFormalization.Section3.T10.Parseval` | Exit 0; 9353 jobs; new module built successfully |
| `lake env lean ../formalization/NSFormalization/Section3/T10/Parseval.lean` | Exit 0; zero output |
| `lake env lean ../research/T10/probes/parseval_closes.lean` | Exit 0; zero output |
| `lake env lean ../research/T10/axioms_parseval.lean` | Exit 0; only nine standard-axiom reports |
| `make check` (worktree root) | Exit 0; plan/contracts/policy/queue pass; 13 policy tests; 45 work items consistent |
| `make test` (worktree root) | Exit 0; registered contract tests pass |
| `make test-mutations` (worktree root) | Exit 0; mutation suite passes |
| `git diff --check` | Exit 0 |

Commit title: `[286-T10] Parseval`.

Handoff: the two Parseval fields can now be filled directly with
`NSFormalization.Section3.T10.parseval_forward` and
`NSFormalization.Section3.T10.parseval_backward`; no other lane is required
for these two fields.
