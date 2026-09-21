# Lane 316 — U7 mean identity

## 1. Theorems (exact target statements)

Namespace `NSFormalization.Section3.T11`; no additional hypothesis.
The two declarations have exactly these API field types:

```lean
  mean_formula : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            velocityMeanT w.velocity t = galileanMeanT a f t
  mean_derivative : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t
```

`mean_formula` follows from U3's public `transformed_mean_zero` by Haar
translation invariance and subtraction of the constant prescribed mean.
U3's proof already integrates momentum, cancels the periodic Laplacian,
pressure gradient and divergence-form advection, differentiates the cube
integral, and uses the initial value plus FTC. `mean_derivative` follows by
FTC on the prescribed mean and local equality on the interior.

## 2. Files

- `formalization/NSFormalization/Section3/T11/MeanIdentity.lean`:
  two exact targets and six elementary adapters in namespace `MeanIdentity`.
- `research/T11/probes/mean_identity_closes.lean`: both verbatim field types
  close; explicit nonzero constant-velocity solution witnesses non-vacuity.
- `research/T11/axioms_mean_identity.lean`: guarded audits of all eight
  declarations, each exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T11/ATTEMPTS_MEAN_IDENTITY.md`: routes, errors and repairs.
- `research/T11/T11_SPLIT.md`: one status line appended to U7.

Existing Lean modules are unchanged. No new instance, named input or heartbeat
option. Small adapters mirror U3's inaccessible private helpers, with attribution;
no private-name escape and no duplication of the momentum integration proof.

## 3. Gaps and error text

No residual mathematical or build gap. Initial elaboration errors (periodicity
metavariable inference and an over-simplified FTC expression) and the initially
unbuilt CriterionBridge dependency are recorded verbatim in ATTEMPTS.
The non-vacuity witness uses nonzero velocity and zero force; no conditional
analytic input is being claimed satisfiable by this example.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`, ran from `verification/`,
and used `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T11.MeanIdentity`: PASS, 9930 jobs,
  zero errors (replayed upstream warnings only).
- `lake build NSFormalization.Section3.T11.CriterionBridge`: PASS; builds
  the non-vacuity witness's datum-construction dependency.
- `lake env lean ../formalization/NSFormalization/Section3/T11/MeanIdentity.lean`:
  PASS, no output.
- `lake env lean ../research/T11/probes/mean_identity_closes.lean`:
  PASS, no output.
- `lake env lean ../research/T11/axioms_mean_identity.lean`:
  PASS, no output; every `#guard_msgs` matched.
- Root `make check`: PASS, including 45 consistent work items.
- Root `LEAN_NUM_THREADS=6 make test`: PASS.
- Root `LEAN_NUM_THREADS=6 make test-mutations`: PASS; all three invalid
  mutations rejected (infrastructure checks, not additional PDE proofs).
- `git diff --check`: PASS.

Local logs: `tmp/mean_build3.log`, `tmp/mean_module.log`,
`tmp/mean_probe_final.log`, `tmp/mean_axioms_final.log`,
`tmp/mean_check.log`, `tmp/mean_test.log`, `tmp/mean_mutations.log`.
