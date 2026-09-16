ACCEPT

## 1. What the lane claims

The worker claims the exact lane-215 input
`shiftedLocalExtension : ShiftedLocalExtension`, an actual glued classical
solution in the strict-extension case, and three corollaries with the
`ShiftedLocalExtension` argument discharged
(`research/A04/REPORT_217.md:5-18`). The claimed mathematics is the restart
step in which a uniformly controlled solution restarted before `S` passes
beyond `S` and uniqueness identifies the overlap
(`paper/sections/appendix-a-local-theory.tex:147-155`).

The report also says that pressure normalization replaces the suggested
cutoff construction, that all fields of `ClassicalSolutionR` are discharged,
that there are no remaining gaps for the shifted extension or its three
consumers, and that the old cross-force/H¹ statement is not claimed
(`research/A04/REPORT_217.md:22-52`). These claims are accurate.

## 2. What is in Lean

### Statement fidelity

The named input is exactly

```lean
def ShiftedLocalExtension : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (w : ClassicalSolutionR ν a f T) (b : ℝ), b ∈ Ico (0 : ℝ) T →
    ∀ L : ℝ, ClassicalSolutionR ν (fun x => w.velocity (b, x)) (timeShift b f) L →
      ENNReal.ofReal (b + L) ≤ maximalLifespanR ν a f
```

at `formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:268-272`.
The delivered theorem has that definition as its literal result type and
splits precisely on `T < b + L`
(`formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:228-233`).
In the strict case, `exists_shifted_glue` constructs
`Nonempty (ClassicalSolutionR ν a f (b + L))`
(`formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:110-115`);
in the other case, the original horizon is enough. This matches the brief and
the paper's restart/uniqueness step.

The alternative pressure construction is sound. `shiftedSolution` really is a
solution with datum `w.velocity (b,·)`, force `timeShift b f`, and horizon
`T-b` (`formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:68-103`).
`velocity_unique_core` gives velocity equality on the common half-open window
(`formalization/NSFormalization/Section4/A02/Uniqueness.lean:78-84`), while
`pressure_gauge_core` supplies the pressure gauge
(`formalization/NSFormalization/Section4/A02/Uniqueness.lean:131-139`).
Basepoint normalization preserves the solution fields
(`formalization/NSFormalization/Section4/A02/Restrict.lean:244-265`) and turns
gauge equivalence into literal equality
(`formalization/NSFormalization/Section4/A02/Restrict.lean:276-287`). The paste
at `c=(b+T)/2` and the two whole-chart equalities are at
`formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:116-149`.

Every local record field from the canonical structure
(`formalization/NSFormalization/Section4/A02/SolutionClass.lean:114-138`) is
filled: horizon/smoothness/initial at
`formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:154-168`,
divergence and momentum at `:169-196`, and Sobolev paths and pressure-gradient
integrability at `:197-226`. The result is fed to the actual supremum definition
(`formalization/NSFormalization/Section4/A02/SolutionClass.lean:140-143`) through
`horizon_le_lifespan`
(`formalization/NSFormalization/Section4/A02/Order.lean:45-51`).

The three report-named corollaries exist with the displayed fixed-force/H⁷,
integral-continuation, and infinite-lifespan statements
(`formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:235-263`).
They apply the lane-215 consumers whose only extra binder is
`extension : ShiftedLocalExtension`
(`formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:276-283,315-323,345-354`).

### Non-vacuity and mutation

There is no silent `⊤.toReal = 0` route in this module and no `.toReal` use at
all. The hypotheses force genuine horizons: each `ClassicalSolutionR` has a
positive horizon (`formalization/NSFormalization/Section4/A02/SolutionClass.lean:119-120`),
and `b ∈ Ico 0 T` gives `b<T`. The conformance example uses `T=2`, `b=1`,
`L=3`, hence a nonempty overlap `[1,2)` and an actual glued horizon `4`
(`research/A04/axioms_shifted_extension.lean:25-30`). The independent copy in
`research/A04/probes/rev217_nonvacuity.lean:8-13` compiled with exit 0 and no
output.

The substantive mutation in
`research/A04/probes/rev217_plus_one_mutation.lean:8-19` changes `b+L` to
`b+L+1` without dropping any argument. The copied proof fails for the expected
horizon mismatch:

```text
../research/A04/probes/rev217_plus_one_mutation.lean:18:30: error: Application type mismatch: The argument
  ⋯.some
has type
  ClassicalSolutionR ν a f (b + L)
but is expected to have type
  ClassicalSolutionR ν a f (b + L + 1)
in the application
  horizon_le_lifespan (exists_shifted_glue hν w hb w₂ h).some
../research/A04/probes/rev217_plus_one_mutation.lean:19:4: error: Type mismatch
  LE.le.trans (ENNReal.ofReal_le_ofReal (le_of_not_gt h)) (horizon_le_lifespan w)
has type
  ENNReal.ofReal (b + L) ≤ maximalLifespanR ν a f
but is expected to have type
  ENNReal.ofReal (b + L + 1) ≤ maximalLifespanR ν a f
```

### Hygiene

The production-module scan for the prohibited proof tokens and
`maxHeartbeats` returned no matches. `git diff --check
origin/erenup/integration...HEAD` returned no output. The exact current commit
delta is:

```text
A	formalization/NSFormalization/Section4/A04/ShiftedExtension.lean
A	research/A04/ATTEMPTS_SHIFTED_EXTENSION.md
M	research/A04/COMPARISON.md
A	research/A04/REPORT_217.md
A	research/A04/axioms_shifted_extension.lean
```

Thus no pre-existing Lean module or contract was modified. The broader
`origin/erenup/integration...HEAD` comparison also lists the inherited lane-215
additions because this lane is based on commit `c41ceba`, but still contains no
modified Lean module. It contains no `verification/` path, so the conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration` gates do not apply. The declaration references in
`ATTEMPTS_SHIFTED_EXTENSION.md:20-34` resolve to the exact uniqueness and gauge
lemmas cited above.

## 3. Gaps

There is no remaining gap in `ShiftedLocalExtension` or in the three requested
corollaries. The report makes no “missing from the tree” claim for these
results. For its separate old cross-force/H¹ caveat, the required whole-tree
search was run:

```text
formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:229:theorem shiftedLocalExtension : ShiftedLocalExtension := by
formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:236:theorem restartBeyond_of_memForceR'
formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:268:def ShiftedLocalExtension : Prop :=
formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:276:theorem restartBeyond_fixed (extension : ShiftedLocalExtension)
formalization/NSFormalization/Section4/A04/Continuation.lean:101:def Restart : Prop :=
formalization/NSFormalization/Section4/A04/Continuation.lean:107:            sobolevENorm 1 (fun x : Space => u (t₀, x)) ≤ K →
formalization/NSFormalization/Section4/A04/Continuation.lean:170:theorem restartBeyond (restart : Restart) :
formalization/NSFormalization/Section4/A04/Continuation.lean:177:            sobolevENorm 1 (fun x : Space => u (t, x)) ≤ K) →
```

This confirms the report's precise point: the H¹/all-force statement exists
only conditionally on the separate `Restart` input
(`formalization/NSFormalization/Section4/A04/Continuation.lean:99-109,166-182`);
lane 217 neither claims nor silently substitutes it.

## 4. Commands and results

Every Lean command sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake from `verification/`.

1. `lake build NSFormalization.Section4.A04.ShiftedExtension` — exit 0. The raw
   command replayed warnings from pre-existing dependencies and ended exactly:

   ```text
   Build completed successfully (10479 jobs).
   ```

   No replayed warning named `ShiftedExtension.lean`. The report's quiet form,
   `lake -q --log-level=error build
   NSFormalization.Section4.A04.ShiftedExtension`, exited 0 with exact output
   `<empty>`.

2. `lake env lean
   ../formalization/NSFormalization/Section4/A04/ShiftedExtension.lean` — exit
   0, exact output `<empty>`.

3. `lake env lean ../research/A04/axioms_shifted_extension.lean` — exit 0;
   exact output:

   ```text
   'NSFormalization.Section4.A04.overlapPaste' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.overlapPaste_left' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.overlapPaste_right' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.contDiffOn_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.continuousOn_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.residual_eq_of_local_slices' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.restarted_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.exists_shifted_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.shiftedLocalExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.restartBeyond_of_memForceR'' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.extendsBeyond_of_memForceR'' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A04.lifespanInfiniteOfLocallyFinite_of_memForceR'' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   ```

4. Root `make check` — exit 0. The command emitted a very large result because
   the architecture checker prints contract closures; exact head/tail (middle
   omitted in accordance with `logs/LESSONS.md`) were:

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 30,
     "source_counts": {
       "formalization": 533,
       "vendor/NavierStokesAndEuler": 2486,
       "vendor/HeliCorgi": 129
     },
     "source_manifest_entries": 2975,
     "missing_copied_imports": [],
     "citation_interfaces_reachable": [],
     "tokens_in_copied_umbrella_closure": [
       {
         "module": "NSFormalization.Paper1.BoundaryCorollary",
         "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
         "line": 90,
         "token": "sorry"
       }
     ],
     "tracked_cache_free": true,
   [reviewer: middle output omitted]
         "NavierStokes.ZerothStressIdentity",
         "TestSupport.Axioms",
         "Tests.GradientL6V2"
       ]
     },
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.043s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

   The copied-source token shown by the checker is the repository-known
   `Paper1/BoundaryCorollary.lean:90`, not this lane or its import closure; the
   checker exits successfully. The lane production module itself has zero
   prohibited-token matches.

For completeness, the report's extra commands were also reproduced:
`lake test` exited 0; `python3
experiments/test_contract_mutations.py --skip-build` exited 0 with

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

Verdict: ACCEPT. Fixes: none.
