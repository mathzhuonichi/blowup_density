ACCEPT

## 1. What the lane claims

The lane claims two registered paper results and three assembly arrows.

1. `T03.non_density` states

   ```lean
   ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
     ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)
   ```

   exactly at `verification/Contracts/V1/TorusNonDensity.lean:59-61`.  This is
   the mathematical assertion of `cor:nondensity`: the paper says non-density
   for every `s ≥ 1/2` and `T > 0` in the relative `L¹_t H^s_x` topology at
   `paper/sections/03-torus.tex:506-508`.  Its proof ingredients—the nonempty
   open radius-`cν` ball, critical regularity, and order lowering—are exactly the
   ones named at `paper/sections/03-torus.tex:511-519` and retained in the
   nine-field record at
   `verification/Contracts/V1/TorusNonDensity.lean:33-55`.

2. `T03.main` states the conjunction of fixed-initial-data density below
   `1/2` and the zero-datum biconditional with `s < 1/2`, exactly at
   `verification/Contracts/V1/TorusMain.lean:39-45`.  These are precisely the
   two clauses at `paper/sections/03-torus.tex:6-16`; the proof identifies the
   two inputs as density and non-density at
   `paper/sections/03-torus.tex:522-524`.  The contract correctly excludes a
   nonzero-datum converse, matching the scope statement at
   `paper/sections/03-torus.tex:525`.

3. The three arrow propositions have the requested types:
   `nonDensityOfCritical` at
   `formalization/NSFormalization/Section3/T21/Assembly.lean:30-32`, and
   `mainOfDensityAndNonDensity` / `mainOfInputs` at
   `formalization/NSFormalization/Section3/T21/MainAssembly.lean:36-41`.
   Their inhabitants are at `Assembly.lean:35-36` and
   `MainAssembly.lean:47-54`.  The longer canonical name
   `mainOfDensityAndNonDensity_arrow_holds` is the documented, necessary
   accommodation for the already-landed field-level theorem of the same base
   name at `formalization/NSFormalization/Section3/T21/Main.lean:107-113`.
   The registered binding has the requested unsuffixed theorem name at
   `verification/Bindings/TorusMain.lean:41-47`.

The registry descriptions are honest: the non-density entry is at
`verification/contracts.json:555-563`, the main entry at
`verification/contracts.json:566-574`, and T21 lists both IDs at
`collaboration/work_items.json:412-420`.

## 2. What is in Lean

The claimed declarations exist with the claimed statements.

- The canonical nine-field `NonDensityAPI` is at
  `formalization/NSFormalization/Section3/T21/Definitions.lean:34-58`; the
  canonical five-field `MainTheoremAPI` is at
  `formalization/NSFormalization/Section3/T21/Main.lean:30-42`.  Field for
  field, these agree with the reconciled Spec at
  `research/T21/Spec.lean:269-431` and `research/T21/Spec.lean:467-559`.
- The two headline propositions agree with the Spec definitions at
  `research/T21/Spec.lean:436-438` and `research/T21/Spec.lean:570-577`.
  The arrow types agree with `research/T21/Spec.lean:595-616`.
- `closedNonDensityAPI` is explicitly indexed by
  `criticalSmallnessH1`, and the only witness-independent conclusion is
  existential, not universal
  (`formalization/NSFormalization/Section3/T21/MainAssembly.lean:56-77`).
  `closedMainTheoremAPI` and both unconditional paper theorems are at
  `MainAssembly.lean:61-86`.
- On the registered side, the lifespan structure exception is handled by the
  proved bridge at `verification/Bindings/TorusNonDensity.lean:32-38`; the
  record uses the registered T20 `K.globalRegularity` directly and assembles
  every remaining field at `verification/Bindings/TorusNonDensity.lean:85-103`.
  The main binding assembles all five fields from registered density and
  non-density at `verification/Bindings/TorusMain.lean:22-39`.
- The public tests expose the two headline declarations and audit their
  axioms at `verification/Tests/TorusNonDensity.lean:20-24` and
  `verification/Tests/TorusMain.lean:17-21`.

No vacuity was found.  The index has the explicit hypothesis `hc : 0 < c`
(`Definitions.lean:35`), T20 supplies it for the selected constant
(`formalization/NSFormalization/Section3/T20/Assembly.lean:27-30`), and the
zero force is a member of every positive-viscosity ball
(`Definitions.lean:40-41`, proved at
`formalization/NSFormalization/Section3/T21/Zero.lean:32-38`).  There is no
`.toReal` in the reviewed T21/contracts/bindings/tests, and no interval
endpoint is used to hide an empty domain.  The `T > 0` input is not needed by
the top-versus-finite contradiction in `Disjointness.lean:20-32`; that helper
is stronger than its paper-facing type, not vacuous.  Likewise, openness is
proved from actual ball membership at `Ball.lean:52-77`; although positivity
of `ν` is not needed for that local implication, positivity is used to put zero
in the ball and hence make it nonempty.

The worker's concrete probe reads off non-density at `ν = T = s = 1` and
subcritical density at the zero datum at
`research/T21/probes/assembly_closes.lean:26-38`.  The additional reviewer
probe proves both that the critical ball is inhabited and that
`breakdownSetTZero 1 1` is inhabited at
`research/T21/probes/rev475_nonvacuity.lean:16-29`.

## 3. Gaps

No lane gap was found.  The worker report makes no "not in the tree" or
missing-lemma claim: its gap section explicitly says there is no proof,
binding, registration, non-vacuity, or axiom gap
(`research/T21/REPORT_475.md:55-57`).  Therefore there is no missing lemma for
which the required whole-`formalization/NSFormalization/Section4` grep could
return evidence.  The listed `q = 2`, regular-reference, and nonzero-datum
items are scope exclusions, not claims that such lemmas are absent from the
tree; they match `paper/sections/03-torus.tex:525` and the registered scopes at
`verification/contracts.json:562-573`.

The substantive negative test changes the zero-datum threshold from `1/2` to
`2/3`, without deleting an argument, at
`research/T21/probes/rev475_main_threshold_mutation.lean:14-17`.  Lean rejects
the existing proof with exactly the expected mismatch:

```text
../research/T21/probes/rev475_main_threshold_mutation.lean:17:2: error: Type mismatch
  closedMainTheoremAPI.zeroInitialDensityIff
has type
  ∀ (nu : ℝ),
    0 < nu →
      ∀ (T : ℝ),
        0 < T →
          ∀ (s : ℝ), RelativelyDenseT 1 s forceClassT ((fun nu T => breakdownSetT nu (fun x => 0) T) nu T) ↔ s < 1 / 2
but is expected to have type
  ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T → ∀ (s : ℝ), RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 2 / 3
```

Hygiene is clean.  The focused declaration scan found no
`sorry`/`admit`/`axiom`/`native_decide`, no `maxHeartbeats`, and no `.toReal`.
The mandated
`git diff --name-only origin/erenup/integration-section3...HEAD` warns that
there are multiple merge bases and uses `0c19e229`; among implementation Lean
files it lists only the added `T21/Main.lean` and `T21/MainAssembly.lean`, plus
the six new contract/binding/test files.  In the worker commit itself,
`Main.lean` has only the lead-authorized dedupe: it imports `T21.Zero`
(`Main.lean:1-2`) and uses the single declaration at
`formalization/NSFormalization/Section3/T21/Zero.lean:41-42`.  No other
existing Lean module was modified.  `git diff --check` returned no output.

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section3.T21.Assembly
[exit 0; no diagnostic from the target module]
Build completed successfully (10689 jobs).

$ lake build NSFormalization.Section3.T21.MainAssembly
[exit 0; no diagnostic from the target module]
Build completed successfully (10744 jobs).
```

Both build invocations replayed pre-existing warnings from upstream modules;
neither printed a warning or error from `Section3/T21/Assembly.lean` or
`MainAssembly.lean`.

```text
$ lake env lean ../formalization/NSFormalization/Section3/T21/Assembly.lean
[exit 0; no output]

$ lake env lean ../formalization/NSFormalization/Section3/T21/MainAssembly.lean
[exit 0; no output]

$ lake env lean ../research/T21/probes/assembly_closes.lean
[exit 0; no output]

$ lake env lean ../research/T21/probes/rev475_nonvacuity.lean
[exit 0; no output]
```

The axiom file contains 41 `#print axioms` commands
(`research/T21/axioms_a.lean:8-54`).  Its complete output was mechanically
normalized and checked:

```text
axiom_outputs: 41
unique_axiom_sets:
  [propext, Classical.choice, Quot.sound]
all_standard: True
```

The focused output from `make check` was:

```text
python3 experiments/check_formalization_plan.py --check
  "task_count": 45,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tracked_cache_free": true,
  "source_hashes_match": false
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
  "registered_contracts": 54,
  "base_compatibility_checked": false,
python3 experiments/test_contract_policy.py
Ran 13 tests in 0.040s
OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Exit status was 0.  `source_hashes_match: false` and the copied-source token
count are repo-wide informational output from the existing plan checker, not a
T21 violation; the focused lane scan above is empty.  The no-base invocation
inside `make check` reports `base_compatibility_checked: false` by design; the
required base-aware command below reports true.

The two new `make test` lines were exactly:

```text
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

`make test-mutations` exited 0; after replayed upstream diagnostics its exact
result was:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

The base-aware contract check exited 0 with:

```text
registered_contracts: 54
base_compatibility_checked: True
scope: 'Architecture checks only; run lake test for Lean type and axiom checks.'
```

The base has 52 entries and the lane has 54:

```text
base_registered_contracts: 52
head_registered_contracts: 54
```

Finally,

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T21.MainAssembly
...
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

The script exited 0.  The reviewer mutation command exited 1 with the expected
error pasted in Part 3; all other commands above exited 0.
