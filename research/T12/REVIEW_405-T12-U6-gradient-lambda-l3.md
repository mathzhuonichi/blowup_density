ACCEPT-WITH-NOTES

## what the lane claims

The worker report claims the API field `gradientLambdaCriticalL3` verbatim, with
`CcriticalThreeHalves = 4 * CcriticalHalf` and `CcriticalThreeHalves_pos`; its
quoted statement is at `research/T12/REPORT_405.md:7-18`.  The canonical field is
indeed exactly the same at `research/T12/probes/api_on_canonical.lean:170-175`,
and the new theorem has the same binder order and both sides at
`formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean:371-376`.
The cited paper estimate is the gradient-plus-Lambda inequality at
`paper/sections/appendix-b-embeddings.tex:26-32` (especially `:30-31`), with
the mean-zero torus qualification at `:21-24`.

The constant and positivity proof are explicit at
`formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean:360-366`.
The `MemPeriodicHomogeneous (3/2) v` input is not used in the proof
(`GradientLambdaL3.lean:371-378`), but it is not silently added: it is part of
the verbatim API field and the resulting theorem is stronger.  There is no
empty-interval or `⊤.toReal` trick.

## what is in Lean

`IsPeriodicLambda v Lv` genuinely supplies `SmoothPeriodicT Lv` and the exact
Fourier graph equation at `formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:92-101`.
Thus the report’s unconditional Lambda half is honest.  The proof derives
mean-zero for derivative columns and Lambda at
`GradientLambdaL3.lean:220-262`, proves the two order shifts at `:264-328`,
and assembles the tensor columns at `:330-356`; the main estimate and constant
assembly are at `:371-405`.  `gradientTensor` is the expected `WithLp 2`
column tensor at `MeanZeroCalculus.lean:82-85`.

The exact API closure is checked by `exact` in
`research/T12/probes/gradient_lambda_l3_closes.lean:36-44`.  The non-vacuity
witness is smooth, periodic, mean-zero, and proved nonzero at
`gradient_lambda_l3_closes.lean:99-149`, with an actual Lambda representative
and conclusion instantiated at `:151-158`.

The whole `formalization/NSFormalization/Section4` tree was searched for the
claimed missing U6 names: no `gradientLambdaCriticalL3`,
`homogeneousENorm_half_dirDeriv_le`, or `homogeneousENorm_half_lambda_le` occurs
there.  The only similarly named result is the distinct whole-space A05 theorem
`velocityCriticalL3` at `formalization/NSFormalization/Section4/A05/CriticalL3.lean:390-410`.

## gaps

There is no mathematical or Lean gap in U6.  The worker accurately records the
separate U4 general-density residual at `research/T12/ATTEMPTS_U4.md:54-86`;
U6 only calls `velocityCriticalL3_smooth` on smooth fields at
`GradientLambdaL3.lean:386-396`, so that residual does not propagate.

The one exact documentation fix is to remove or update the fallback sentence at
`research/T12/REPORT_405.md:60`: it says that `REPORT_405.md` could not be
written, while that report file is present in this lane.  No code change is
required.

The substantive negative mutation is in reviewer probe
`research/T12/probes/rev405_negative.lean:1-11`: changing the RHS constant to
`CcriticalThreeHalves - 1` fails at line 10 with:

```
error: Type mismatch
  gradientLambdaCriticalL3 v Lv hv hm hL
has type ... ENNReal.ofReal CcriticalThreeHalves * periodicHomogeneousENorm (3 / 2) v
but is expected to have type ... ENNReal.ofReal (CcriticalThreeHalves - 1) * periodicHomogeneousENorm (3 / 2) v
```

This changes a main constant, not merely an argument.  Grep of the module and
closure probe found no `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats`; `git diff --check` is clean.

## commands and results

All Lean commands below used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`,
and ran `lake` from `verification/`:

- `lake build NSFormalization.Section3.T12.GradientLambdaL3` — exact final
  output: `Build completed successfully (10040 jobs).`  Only replayed,
  pre-existing dependency linter warnings appeared.
- `lake env lean ../formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean`
  — 0 output.
- `lake env lean ../research/T12/probes/gradient_lambda_l3_closes.lean` — 0 output.
- `lake env lean ../research/T12/axioms_u6.lean` — 24/24 declarations report
  exactly `[propext, Classical.choice, Quot.sound]`.
- `lake env lean ../research/T12/probes/rev405_negative.lean` — expected
  nonzero exit; exact error is the `Type mismatch` shown in **gaps** above.
- `make check` from the repository root — exit 0; exact summary lines were
  `.............`, `OK`, and
  `45 work items: ownership, contract registration and task cards consistent.`
- `BASE_REF=origin/erenup/integration-section3 scripts/gates.sh NSFormalization.Section3.T12.GradientLambdaL3`
  — exact final output `== gates OK`; its mutation tail was
  `extra_axiom: rejected as required`, `weakened_hypothesis: rejected as required`,
  `Mutation suite passed. This is an infrastructure check, not a PDE proof.`
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
  — exact result includes `base_compatibility_checked: true`.
- `git diff --name-only origin/erenup/integration-section3...HEAD` —
  `formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean`,
  `logs/LESSONS.md`, `research/T12/ATTEMPTS_U6.md`,
  `research/T12/REPORT_405.md`, `research/T12/T12_SPLIT.md`,
  `research/T12/axioms_u6.lean`, and
  `research/T12/probes/gradient_lambda_l3_closes.lean`; no pre-existing Lean
  module is modified.

ACCEPT-WITH-NOTES — fix the stale one-line fallback sentence at `research/T12/REPORT_405.md:60`; no mathematical or Lean fix is required.
