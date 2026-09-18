ACCEPT-WITH-NOTES

Exact one-line fix: replace `research/T11/T11_SPLIT.md:54` by

```markdown
  **Status (309): complete — all-real-order datum existence/finiteness, exact norm identification, restricted-time measurability, and both criterion directions proved without named input; see `REPORT_309.md`.**
```

This closes the unmatched Markdown emphasis. It is cosmetic and does not affect the Lean verdict.

## 1. What the lane claims

The worker reports ten declarations in namespace `NSFormalization.Section3.T11`
at `research/T11/REPORT_309.md:8`--`research/T11/REPORT_309.md:52`. Each exists
with the reported statement:

- `periodicSobolevENorm_eq_datum`: report `:8`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:17`.
- `exists_periodicDatum_smooth`: report `:12`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:27`.
- `periodicSobolevENorm_ne_top_smooth`: report `:16`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:57`.
- `norm_periodicDatum`: report `:20`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:65`.
- `periodicSobolevENorm_eq_of_datum`: report `:24`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:84`.
- `periodicSobolevENorm_eq_smooth`: report `:29`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:91`.
- `continuousOn_periodicSobolevENorm`: report `:35`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:100`.
- `aemeasurable_periodicSobolevENorm`: report `:40`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:110`.
- `continuousOn_h2SquaredProfile`: report `:45`, implementation
  `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:118`.
- `squaredHTwoIntegralT_ne_top_iff_finiteH2Energy`: report `:49`,
  implementation `formalization/NSFormalization/Section3/T11/CriterionBridge.lean:128`.

The exact-statement conformance examples cover the same ten declarations at
`research/T11/probes/criterion_bridge_closes.lean:16`--`:70`, and the file
typechecks with zero output. Thus this is not merely a name match.

The statements are faithful to U2 at `research/T11/T11_SPLIT.md:45`--`:53`:

- The paper defines the torus `H^s` norm with weight
  `(1+4π²|k|²)^s` and sums squared vector components at
  `paper/sections/01-introduction.tex:80`--`:103`. The canonical datum uses
  exactly the weighted coefficients and Haar-integrability at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:104`--`:120`.
  The construction at `CriterionBridge.lean:27`--`:54` uses the actual
  all-real-order scalar representative
  `formalization/NSFormalization/Paper1/PeriodicSmoothSobolev.lean:45`, proves
  conjugate symmetry, and proves Haar-integrability. Finiteness then follows
  at `CriterionBridge.lean:57`--`:62` without a `toReal` escape hatch.
- Datum uniqueness is the proved canonical theorem at
  `formalization/NSFormalization/Section3/T10/DatumBasics.lean:129`, and it is
  the declaration installed in registered contract `T01.torus_data` at
  `verification/Bindings/TorusData.lean:149`. Its use at
  `CriterionBridge.lean:17`--`:24`, followed by the norm computation at
  `CriterionBridge.lean:65`--`:88`, yields the requested exact `ENNReal.ofReal`
  identity. This agrees with the scalar norm theorem at
  `formalization/NSFormalization/Paper1/PeriodicSmoothSobolev.lean:53`.
- `ClassicalSolutionT.sobolev` really supplies a continuous datum path on
  `Ico 0 T` at `formalization/NSFormalization/Section3/T10/PeriodicData.lean:286`.
  The lane transfers it to continuity and then restricted-measure
  a.e.-measurability at `CriterionBridge.lean:99`--`:115`. This restriction is
  mathematically necessary because the solution structure constrains the
  velocity only on its lifespan.
- The manuscript criterion is precisely finiteness of
  `∫₀^S ‖u(t)‖_{H²}² dt` at `paper/sections/02-preliminaries.tex:105`--`:114`.
  The T11 lintegral is defined on `Ioo 0 S` at
  `formalization/NSFormalization/Section3/T11/LocalTheory.lean:58`, while
  `FiniteH2Energy` is real-valued `IntegrableOn` over `Ioc 0 S` at
  `formalization/NSFormalization/Paper1/PeriodicLocalLifespan.lean:52`--`:62`.
  The proof at `CriterionBridge.lean:128`--`:148` identifies the integrands,
  supplies measurability, and uses equality of the two restricted Lebesgue
  measures, so both directions—not just the easy one—are present. The imported
  bridge's advertised minimal wrapper is indeed at
  `formalization/NSFormalization/Paper1/PeriodicFiniteH2Bridge.lean:25`.

No theorem is made vacuous by an empty time interval: every
`ClassicalSolutionT` carries `0 < T` at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:270`. There is no
use of `⊤.toReal = 0`, no unused theorem binder, and no residual named input.

## 2. What is in Lean

The implementation proves all four requested pieces unconditionally:
all-real-order datum existence and finiteness (`CriterionBridge.lean:27`--`:62`),
exact datum/norm identification (`:65`--`:97`), solution-interval continuity
and a.e.-measurability (`:100`--`:124`), and the two-way H² criterion bridge
(`:128`--`:148`). `toFlow` preserves the velocity definitionally at
`formalization/NSFormalization/Section3/T11/FlowConversion.lean:43`--`:55`, so
the last theorem compares the same physical field.

The worker's non-vacuity example is universal over constant vectors at
`CriterionBridge.lean:150`. The reviewer strengthened this check: the witness
`coordinateVector 0` is proved nonzero at
`research/T11/probes/rev309_nonvacuity.lean:12`, and its extended norm is finite
for every real order at `research/T11/probes/rev309_nonvacuity.lean:19`. That
probe typechecks with zero output.

The substantive negative probe changes the H² lintegral to H³ while retaining
the H²-energy predicate at `research/T11/probes/rev309_h3_mutation.lean:15`.
The original theorem fails to prove the mutation at line 20 with the expected
type mismatch; this is a changed constant in the main criterion, not a dropped
argument.

## 3. Gaps

There is no mathematical or Lean gap, and the worker makes no “not in the
tree” claim (`research/T11/REPORT_309.md:64`--`:66` and
`research/T11/ATTEMPTS_CRITERION_BRIDGE.md:3`--`:8`). Consequently the mandated
whole-`Section4` missing-lemma grep has no claim to test.

The only finding is cosmetic: `research/T11/T11_SPLIT.md:54` opens bold
emphasis with `**Status` but never closes it. Apply the exact one-line
replacement printed immediately below the verdict. No Lean fix is requested.

Hygiene passes. Against `origin/erenup/integration-section3`, the only
formalization module in the diff is the new
`formalization/NSFormalization/Section3/T11/CriterionBridge.lean`; no existing
Lean module or `verification/` file was modified. The changed Lean files contain
no whole-word `sorry`, `admit`, `axiom`, or `native_decide`, no
`maxHeartbeats`, and no instance declaration. `git diff --check` is silent.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran from `verification/`.

1. `lake build NSFormalization.Section3.T11.CriterionBridge` — exit 0. Exact
   head/tail (the omitted middle consists solely of replayed warnings from
   pre-existing dependency files):

   ```text
   ⚠ [8778/9047] Replayed NSFormalization.Source.FiniteHilbertBochner
   warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
   ... pre-existing replayed dependency warnings omitted ...
   ⚠ [9960/9967] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
   warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:100:23: Variable name `U` is not explicitly referenced.
   ... final pre-existing dependency warnings omitted ...
   Build completed successfully (9967 jobs).
   ```

   There is no diagnostic from `CriterionBridge.lean` itself.

2. Direct checks — all exit 0 with exact output `<no output>`:

   ```text
   lake env lean ../formalization/NSFormalization/Section3/T11/CriterionBridge.lean
   <no output>
   lake env lean ../research/T11/probes/criterion_bridge_closes.lean
   <no output>
   lake env lean ../research/T11/probes/rev309_nonvacuity.lean
   <no output>
   ```

3. `lake env lean ../research/T11/axioms_criterion_bridge.lean` — exit 0,
   exact output:

   ```text
   'NSFormalization.Section3.T11.periodicSobolevENorm_eq_datum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.exists_periodicDatum_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.periodicSobolevENorm_ne_top_smooth' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T11.norm_periodicDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.periodicSobolevENorm_eq_of_datum' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T11.periodicSobolevENorm_eq_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.continuousOn_periodicSobolevENorm' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T11.aemeasurable_periodicSobolevENorm' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T11.continuousOn_h2SquaredProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.squaredHTwoIntegralT_ne_top_iff_finiteH2Energy' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   ```

4. `make check` from the worktree root — exit 0. Exact head/tail (the contract
   closure JSON in the middle was 736093 bytes):

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 45,
     "source_counts": {
       "formalization": 563,
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
     "source_hashes_match": false
   }
   Explicit axiom/admission tokens, all copied sources: 11
   python3 experiments/check_contracts.py
   ... 736093-byte contract-closure JSON omitted ...
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.045s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

5. Negative check:

   ```text
   $ lake env lean ../research/T11/probes/rev309_h3_mutation.lean
   ../research/T11/probes/rev309_h3_mutation.lean:20:2: error: Type mismatch
     squaredHTwoIntegralT_ne_top_iff_finiteH2Energy w
   has type
     squaredHTwoIntegralT S w.velocity ≠ ∞ ↔ FiniteH2Energy (toFlow w)
   but is expected to have type
     ∫⁻ (t : ℝ) in Ioo 0 S, (periodicSobolevENorm 3 fun x => w.velocity (t, x)) ^ 2 ≠ ∞ ↔ FiniteH2Energy (toFlow w)
   ```

   Exit status was 1, as expected.

6. Hygiene commands:

   ```text
   $ git diff --check origin/erenup/integration-section3...HEAD
   <no output>
   $ rg -n --glob '*.lean' '\b(sorry|admit|axiom|native_decide)\b' <lane Lean files>
   <no output>
   $ rg -n 'maxHeartbeats|(^|[^[:alnum:]_])instance([[:space:]]|$)' <lane Lean files>
   <no output>
   $ git diff --name-only origin/erenup/integration-section3...HEAD
   formalization/NSFormalization/Section3/T11/CriterionBridge.lean
   research/T11/ATTEMPTS_CRITERION_BRIDGE.md
   research/T11/REPORT_309.md
   research/T11/T11_SPLIT.md
   research/T11/axioms_criterion_bridge.lean
   research/T11/probes/criterion_bridge_closes.lean
   ```

`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` are
conditional on touching `verification/`; the diff above shows that this lane
did not, so those two conditional gates were not run.
