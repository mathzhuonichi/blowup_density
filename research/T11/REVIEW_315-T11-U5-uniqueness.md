ACCEPT

# Review 315-T11-U5-uniqueness

## 1. What the lane claims

The worker claims three U5 declarations with no peeled/named analytic input:
pointwise velocity and pressure uniqueness on the common half-open interval,
and the selected local horizon's order relation to the T10 maximal lifespan
(the last explicitly takes the API's preceding `solution` field).  The
reported statements are at `research/T11/REPORT_315.md:6-35`,
the claimed proof routes are at `research/T11/REPORT_315.md:38-43`, and the
explicit no-gap/no-input claim is at `research/T11/REPORT_315.md:57-60`.

These are the mathematics requested by the brief:

- The manuscript fixes periodic pressure by `∫_T³ p = 0` and says local
  uniqueness defines the maximal classical lifespan at
  `paper/sections/02-preliminaries.tex:28-33`.  Its proposition asserts a
  unique maximal smooth velocity, with pressure determined by that convention,
  at `paper/sections/02-preliminaries.tex:105-109`.
- The paper's common-interval difference-energy proof is stated at
  `paper/sections/appendix-a-local-theory.tex:115-125`: for two solutions with
  the same data, Grönwall gives uniqueness, then the local solutions patch to
  define the maximal lifespan.
- The exact API fields are
  `research/T11/probes/api_on_canonical.lean:67-84`.  Their quantifiers,
  hypotheses, `Ico (0 : ℝ) (min T₁ T₂)` domains, pointwise conclusions, and
  `ENNReal.ofReal` lifespan conclusion agree textually with the worker's three
  reported statements.

The report also claims a non-vacuity witness at
`research/T11/REPORT_315.md:49-50`; the actual witness occupies
`research/T11/probes/uniqueness_closes.lean:47-112`.

## 2. What is in Lean

### Statement fidelity and proofs

- `velocity_unique` is declared at
  `formalization/NSFormalization/Section3/T11/Uniqueness.lean:27-35`.  It is
  exactly the API field at `research/T11/probes/api_on_canonical.lean:67-73`.
  `toFlow` preserves velocity, pressure, and all fields needed by the older
  flow at `formalization/NSFormalization/Section3/T11/FlowConversion.lean:44-55`.
  The invoked theorem has exactly the claimed common interval and pointwise
  conclusion at
  `formalization/NSFormalization/Paper1/PeriodicLocalLifespan.lean:175-179`.
- `pressure_unique` is declared at
  `formalization/NSFormalization/Section3/T11/Uniqueness.lean:38-56` and is
  exactly the API field at `research/T11/probes/api_on_canonical.lean:74-80`.
  T10's gauge is the Haar integral at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:249-256,299`;
  its torus lift is the reducible Paper 1 alias at the same file's lines
  `35-50`.  `integral_torusLift` identifies that integral with `cubeIntegral`
  at `formalization/NSFormalization/Paper1/TorusCube.lean:39-42`.
  `IsNormalized` is precisely vanishing of this cube integral on the flow
  horizon at
  `formalization/NSFormalization/Paper1/PeriodicLocalLifespan.lean:43-46`, and
  `normalized_flows_agree` returns both pointwise equalities on the exact common
  interval at the same file's lines `227-235`.  Thus lines 46-56 of the lane
  honestly construct both normalization premises and select the pressure
  component.
- `horizon_le_lifespan` is declared at
  `formalization/NSFormalization/Section3/T11/Uniqueness.lean:60-72`.  Supplying
  the preceding API `solution` field explicitly leaves exactly the API
  conclusion at `research/T11/probes/api_on_canonical.lean:81-84`.
  `maximalLifespanT` is the stated double supremum at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:301-304`, so the
  two `le_iSup_of_le` applications are definitionally the requested witness
  argument and require no conversion.

### Satisfiability and hypotheses

There is no hidden `⊤.toReal = 0`, empty-interval trick, or named analytic
premise.  Every `ClassicalSolutionT` carries `0 < T` at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-274`, so a
pair of such solutions has a positive common horizon.  The initial/force class
premises are unused in the first two proof terms
(`formalization/NSFormalization/Section3/T11/Uniqueness.lean:34,45`) because
the exact API retains them while the two already-constructed solution records
contain everything uniqueness consumes.  They are not vacuity assumptions:

- the probe constructs a nonzero constant datum and zero force, proving their
  class memberships at `research/T11/probes/uniqueness_closes.lean:58-72`;
- it constructs an actual positive-horizon `ClassicalSolutionT 1 a f 1` at
  `research/T11/probes/uniqueness_closes.lean:73-105`;
- nonzeroness is proved at `research/T11/probes/uniqueness_closes.lean:61-64`
  and used at line 111; both uniqueness declarations and the nontrivial
  lifespan lower bound are instantiated at lines 106-112.

The exact-shape closure checks are at
`research/T11/probes/uniqueness_closes.lean:17-45`.  The guarded axiom audit is
at `research/T11/axioms_uniqueness.lean:7-17`; an independent unguarded reviewer
probe at `research/T11/probes/rev315_axioms.lean:5-7` confirms every declaration
uses exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and hygiene

No mathematical or Lean gap was found.  In particular, the report does not
declare any lemma "not in the tree" (`research/T11/REPORT_315.md:57-60` says
there is no proof gap), so the requested conditional whole-Section4 grep has no
missing-lemma claim to test.

The base comparison lists exactly:

```text
formalization/NSFormalization/Section3/T11/Uniqueness.lean
research/T11/ATTEMPTS_UNIQUENESS.md
research/T11/REPORT_315.md
research/T11/T11_SPLIT.md
research/T11/axioms_uniqueness.lean
research/T11/probes/uniqueness_closes.lean
```

Thus no existing `formalization/**/*.lean` or `verification/**/*.lean` module
was modified; the only existing file changed is the brief-authorized append to
the research split record.  `git diff --check` is clean.  A scan of all three
lane Lean files and both reviewer probes finds no declaration/use of `sorry`,
`admit`, `axiom`, `native_decide`, `maxHeartbeats`, or anonymous/local
instances.  No named `def ... : Prop` input was added.  The citations in the
worker report resolve to declarations with the advertised statements, as
documented in Part 2.

The reviewer negative probe
`research/T11/probes/rev315_widen_interval.lean:18-25` substantively changes
the main velocity statement by widening `min T₁ T₂` to `max T₁ T₂`.  It fails
for the expected reason: the proved theorem only covers the common interval.

`verification/` is absent from the lane diff.  Therefore the brief's
conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates are
not applicable.  (`make check` still ran its ordinary architecture contract
check and passed.)

## 4. Commands and results

All Lean/Lake commands were run after `. scripts/lean-env.sh`; Lake was invoked
only from `verification/`, with `LEAN_NUM_THREADS=6`.

### Module build

Command:

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Uniqueness
```

Result: exit 0.  Exact output head/tail follows; the omitted middle consists
only of replayed warnings from pre-existing dependency files and contains no
`Uniqueness.lean` diagnostic.

```text
⚠ [8778/9091] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

[... replayed dependency warnings omitted ...]

⚠ [9955/9957] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:100:23: Variable name `U` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _U

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:325:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:335:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9957 jobs).
```

### Direct Lean checks

Commands:

```text
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/Uniqueness.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/uniqueness_closes.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_uniqueness.lean
```

Each command exited 0 with exactly zero output.

The independent unguarded audit command

```text
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/rev315_axioms.lean
```

exited 0 with exact output:

```text
'NSFormalization.Section3.T11.velocity_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.pressure_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.horizon_le_lifespan' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Negative mutation

Command:

```text
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/rev315_widen_interval.lean
```

Result: expected exit 1, with exact output:

```text
../research/T11/probes/rev315_widen_interval.lean:25:2: error: Type mismatch
  velocity_unique
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁) (u₂ : ClassicalSolutionT ν a f T₂),
            ∀ t ∈ Ico 0 (min T₁ T₂), ∀ (x : Space), u₁.velocity (t, x) = u₂.velocity (t, x)
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁) (u₂ : ClassicalSolutionT ν a f T₂),
            ∀ t ∈ Ico 0 (max T₁ T₂), ∀ (x : Space), u₁.velocity (t, x) = u₂.velocity (t, x)
```

### Repository check

Command: `make check` from the worktree root after sourcing the environment.
Result: exit 0.  Per the top-of-file `logs/LESSONS.md` rule against embedding
enormous check JSON, here are the exact first and last 20 output lines; 43,293
middle lines were omitted.

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 568,
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
[... 43293 middle lines omitted ...]
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.TorusData"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

### Hygiene commands

`git diff --name-only origin/erenup/integration-section3...HEAD` produced the
six-file list printed in Part 3.  Restricting that command to `verification/`
or to modified `formalization/**/*.lean` files produced exactly zero output.
`git diff --check origin/erenup/integration-section3...HEAD` also exited 0 with
zero output.  The prohibited-token/heartbeat/instance scans described in Part
3 exited with the expected no-match status and zero output.

Fixes required: none.
