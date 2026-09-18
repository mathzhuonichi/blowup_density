ACCEPT-WITH-NOTES

## What the lane claims

`research/T15/REPORT_364.md:11-19` claims the measure-free restricted-cube bridge and Goal 1; `:25-30` claims the gradient companion; `:34-38` claims the per-slice corollary.  The report also claims the ten declarations listed at `:40-47`, standard three-axiom audits at `:5-7,61`, and a concrete non-vacuity probe at `:57-60`.

The mathematics is the requested single-copy endpoint.  The paper says that at order zero the torus and Euclidean (L^2) norms agree and that the corresponding gradient equality holds at order one (`paper/sections/03-torus.tex:22-30`), and the scaling proposition uses exactly these energy quantities (`paper/sections/03-torus.tex:122-138`).  The lane brief's U-TB1 route is recorded at `research/T15/T15_SPLIT.md:38-42,69-74`.

## What is in Lean

Every declaration claimed in the worker report exists with the claimed type:

- `lintegral_enorm_torusLift` is the arbitrary-field, arbitrary-real-power bridge at `formalization/NSFormalization/Section3/T15/HaarBridge.lean:66-84`.
- `eLpNorm_torusLift_restrict` is the restricted-cube `eLpNorm` equality at `HaarBridge.lean:87-98`.
- The interior single-copy helpers `periodize_eq_of_mem_interior`, `periodize_eventuallyEq_interior`, and `eLpNorm_periodize_restrict_eq` are at `HaarBridge.lean:102-145`.
- Goal 1, including the stated `ContDiff` binder (named `_hf` and intentionally unused), is exactly `eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure = eLpNorm f 2 volume` at `HaarBridge.lean:154-158`.  The worker openly discloses the weakening at `research/T15/REPORT_364.md:49-53`; the support premise is still genuine and load-bearing.
- `eLpNorm_gradientVector_eq_gradientENorm` is the reported vector-gradient identity for arbitrary `μ` at `HaarBridge.lean:169-194`, and `gradientENorm_restrict_eq` is the support reduction at `:199-211`.
- Goal 2 is exactly the `I02.spatialGradient`/T10-compatible per-slice norm against T13's `gradientENorm f volume` at `HaarBridge.lean:216-243`.  This matches `energyGradientT`'s integrand (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:334-337`) and T13's gradient definition (`formalization/NSFormalization/Section3/T13/Localization.lean:84-88`).
- Goal 3 is the per-slice corollary at `HaarBridge.lean:249-254`.

The proof uses the cited tree facts honestly: `endpoint_zero_eq` is at `formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean:364-374`, `endpoint_one_eq` and its a.e. derivative argument are at `:376-397`, the existing neighbourhood derivative bridge is at `:340-347`, and the Haar/cube facts are `formalization/NSFormalization/Section3/T13/TorusIdentity.lean:402-415,419-436,459-461`.  The new measure-free route is stronger than the continuous-integrand route and does not smuggle in measurability.

The lane closure probe typechecks all three goals (`research/T15/probes/haar_bridge_closes.lean:82-104`).  Its comments call the bump field nonzero, but the file does not itself prove that fact; my independent reviewer probe proves the same concrete bump is nonzero (`research/T15/probes/rev364_nonvacuity.lean:14-35`).

## Gaps

There is no mathematical or statement-fidelity gap in U-TB1.  The `ContDiff` hypothesis on Goal 1 is redundant but explicitly named `_hf` and documented, rather than silently used to make the target vacuous.  Goal 2 genuinely uses smoothness of `f` in `eLpNorm_gradientVector_eq_gradientENorm`; it does not assume smoothness of `periodize f`, and the frontier is handled by the null-set/a.e. argument at `HaarBridge.lean:222-243`.

The report's deferred `periodize`-smoothness discussion is outside this unit.  The required whole-tree searches found no pre-existing U-TB1 bridge under `formalization/NSFormalization/Section4`, `Section3/T10`, `Section3/T13`, `verification/Contracts/V1/Scaling.lean`, or `verification/Bindings/Scaling.lean`; the only matching Section-4 names are the already cited gradient endpoint declarations.  Thus no “not in the tree” claim hides an existing missing theorem.

For the requested lessons audit, I read the first 40 lines and explicitly tracked its named instances: lanes 353, 350, 343, 340, 334, 322/327, 329, 326, 325, 305, 293, 283, 221/223, 251, 260, 239, 294, 180, 190, and 158–169 (plus the documented PR/worktree cases #294, #260, and #239).

The substantive negative probe changes the right-hand side by a factor of two (`research/T15/probes/rev364_mutation.lean:15-21`).  It fails for the expected reason, not because an argument was dropped:

```text
../research/T15/probes/rev364_mutation.lean:21:2: error: Type mismatch
  eLpNorm_torusLift_periodize f hf hsupp
has type
  eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure = eLpNorm f 2 volume
but is expected to have type
  eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure = 2 * eLpNorm f 2 volume
```

Hygiene passes: the production module has no executable `sorry`, `admit`, `axiom`, or `native_decide`, no `maxHeartbeats` override, and `git diff --check` is clean.  The one documentation/non-vacuity note is the unproved “nonzero” wording in `haar_bridge_closes.lean:36-40`; the exact fix is to add the explicit `probeField_ne_zero` lemma (as in the reviewer probe) or change those comments to say only “explicit smooth field.”  The worker report also omits the module `lake env lean` command from its command list; add that one command to `research/T15/REPORT_364.md:81-91`.

## Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`, one `lake` process at a time, and `lake` only from `verification/`.  `verification/.lake/packages` is the expected symlink to the shared cache.

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.HaarBridge` — exit 0.  The target produced no diagnostic (`grep HaarBridge /tmp/rev364_build.log` was empty).  The exact final output was:

  ```text
  Build completed successfully (9914 jobs).
  ```

  The other output consists only of replayed dependency linter/info messages (for example the final replayed `Paper3.SobolevDirectionalDerivative` warning); no warning originates in HaarBridge.

* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T15/HaarBridge.lean` — exit 0, exact output: empty.

* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/haar_bridge_closes.lean` — exit 0, exact output: empty.

* `cd verification && lake env lean ../research/T15/probes/rev364_nonvacuity.lean` — exit 0, exact output: empty.

* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T15/axioms_utb1.lean` — exit 0.  Exact declarations printed (Lean wraps long entries across lines):

  ```text
  'NSFormalization.Section3.T15.lintegral_enorm_torusLift' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T15.eLpNorm_torusLift_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T15.periodize_eq_of_mem_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T15.periodize_eventuallyEq_interior' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'NSFormalization.Section3.T15.eLpNorm_periodize_restrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T15.eLpNorm_torusLift_periodize' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T15.eLpNorm_gradientVector_eq_gradientENorm' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'NSFormalization.Section3.T15.gradientENorm_restrict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T15.eLpNorm_torusLift_spatialGradient_periodize' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'NSFormalization.Section3.T15.eLpNorm_torusLift_periodize_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

* `make check` — exit 0.  Exact final output:

  ```text
  python3 experiments/test_contract_policy.py
  .............
  ----------------------------------------------------------------------
  Ran 13 tests in 0.044s

  OK
  python3 experiments/check_work_queue.py
  45 work items: ownership, contract registration and task cards consistent.
  ```

* `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T15.HaarBridge` — exit 0; exact final output:

  ```text
  == make test-mutations
  extra_axiom: rejected as required
  weakened_hypothesis: rejected as required
  Mutation suite passed. This is an infrastructure check, not a PDE proof.
  == check_contracts
    "base_compatibility_checked": true,
    "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
  }
  == gates OK
  ```

* `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` — exit 0; exact tail:

  ```text
    "base_compatibility_checked": true,
    "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
  }
  ```

* `cd verification && lake env lean ../research/T15/probes/rev364_mutation.lean` — expected exit 1 with the type-mismatch error reproduced above.

* `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the new HaarBridge/research artifacts plus the authorized `research/T15/T15_SPLIT.md` status update; no existing formalization module or verification file is modified.  Reviewer-only additions are the two `research/T15/probes/rev364_*.lean` probes and this report.

Fixes: add the explicit nonzero witness lemma (or soften the probe's “nonzero” comments), and record the omitted module `lake env lean` command in the worker report.
