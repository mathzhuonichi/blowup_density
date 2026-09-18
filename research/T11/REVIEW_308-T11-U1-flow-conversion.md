ACCEPT

## 1. What the lane claims

The worker claims two definitional spelling bridges, fieldwise conversions in
both directions, two full round trips, four data-field simp lemmas, and the
one-way force-class transport (`research/T11/REPORT_308.md:7-47`).  Those are
exactly the U1 obligations in the binding split
(`research/T11/T11_SPLIT.md:37-44`, `research/T11/T11_SPLIT.md:175-194`).

The mathematical representations agree with the manuscript.  The paper makes
torus velocity and pressure periodic, imposes zero pressure mean, and requires
the velocity to be continuous in every integer Sobolev order on compact
lifespan intervals (`paper/sections/02-preliminaries.tex:28-31`); it defines the
torus force class as smooth, periodic, compactly supported in positive time
(`paper/sections/02-preliminaries.tex:7-10`,
`paper/sections/02-preliminaries.tex:22-26`).  U1 does not assert new analytic
existence: it only reconciles two Lean representations of such a solution.

No hypothesis has been added or hidden:

- `Flow` has exactly eleven fields (`formalization/NSFormalization/Paper1/PeriodicLifespan.lean:12-23`).
  All eleven are copied by `toFlow`
  (`formalization/NSFormalization/Section3/T11/FlowConversion.lean:43-55`).
- `ClassicalSolutionT` has those eleven shared fields and exactly three extra
  fields, `sobolev`, `pressure_gradient`, and `pressure_gauge`
  (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-299`).
  `ofFlow` takes precisely those three fields with their canonical types and
  consumes each one (`formalization/NSFormalization/Section3/T11/FlowConversion.lean:57-82`).
- Both source structures contain `horizon_pos : 0 < T`
  (`formalization/NSFormalization/Paper1/PeriodicLifespan.lean:15`,
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:270-271`), so
  the slab obligations are not discharged by silently choosing an empty
  nonpositive horizon.  There is no `ENNReal.toReal` statement or unused
  theorem binder in this lane.
- The force theorem assumes the exact T10 class
  (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:237-242`) and
  concludes the strictly weaker Paper-1 class
  (`formalization/NSFormalization/Paper1/PeriodicLocalLifespan.lean:31-36`).
  Its compact-support component is intentionally unnecessary for the weaker
  conclusion; smoothness and periodicity are both used
  (`formalization/NSFormalization/Section3/T11/FlowConversion.lean:120-125`).

The report's zero-force non-vacuity instance is real: it explicitly constructs
the `MemForceT 0` premise before applying transport
(`research/T11/probes/flow_conversion_roundtrip.lean:64-71`), and the probe
typechecks with no output.  No named input `def ... : Prop` is present or
needed.

## 2. What is in Lean

Every reported declaration exists with the reported statement:

- `source_residual_eq_navierStokesResidual` is at
  `formalization/NSFormalization/Section3/T11/FlowConversion.lean:28-33`.
  The two bodies have the same signs, viscosity placement, and summands at
  `formalization/NSFormalization/Source/Insertion.lean:20-24` and
  `vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:55-62`;
  hence `rfl` is faithful.
- `isPeriodicOn_iff_unitSpatialPeriodsOn` is at
  `formalization/NSFormalization/Section3/T11/FlowConversion.lean:35-39`.
  The definitions are token-equivalent at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:60-64` and
  `vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:47-51`.
- `toFlow` and `ofFlow` are at
  `formalization/NSFormalization/Section3/T11/FlowConversion.lean:43-82`.
  The interval choices remain exactly `Ico 0 T` for slab fields and `Ioo 0 T`
  for the equation, matching both structures.
- The four reported data-field simp lemmas are at
  `formalization/NSFormalization/Section3/T11/FlowConversion.lean:84-102`.
- `toFlow_ofFlow` and `ofFlow_toFlow` are full structure equalities at
  `formalization/NSFormalization/Section3/T11/FlowConversion.lean:104-116`,
  not merely projection-by-projection surrogates.  The exact target-shaped
  applications are also checked at
  `research/T11/probes/flow_conversion_roundtrip.lean:50-58`.
- `memForceT_to_isSmoothPeriodicForce` has the reported direction and exact
  type at `formalization/NSFormalization/Section3/T11/FlowConversion.lean:118-125`.

The omitted lifespan equality is not a missing U1 deliverable.  The split
explicitly says it is not available from `toFlow` alone and assigns the reverse
direction/equality to U15 after the three extra fields can be supplied at every
horizon (`research/T11/T11_SPLIT.md:123-129`,
`research/T11/T11_SPLIT.md:194`).

Hygiene results:

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
formalization/NSFormalization/Section3/T11/FlowConversion.lean
research/T11/ATTEMPTS_FLOW_CONVERSION.md
research/T11/REPORT_308.md
research/T11/T11_SPLIT.md
research/T11/axioms_flow_conversion.lean
research/T11/probes/flow_conversion_roundtrip.lean

$ git diff --name-only --diff-filter=M origin/erenup/integration-section3...HEAD -- '*.lean'
<no output>

$ git diff --name-only origin/erenup/integration-section3...HEAD -- verification
<no output>

$ git diff --check origin/erenup/integration-section3...HEAD
<no output>

$ rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom\b|set_option[[:space:]]+maxHeartbeats' \
    formalization/NSFormalization/Section3/T11/FlowConversion.lean \
    research/T11/probes/flow_conversion_roundtrip.lean \
    research/T11/axioms_flow_conversion.lean
<no output>

$ rg -n '^[[:space:]]*(local[[:space:]]+)?instance([[:space:]]|:)' \
    formalization/NSFormalization/Section3/T11/FlowConversion.lean \
    research/T11/probes/flow_conversion_roundtrip.lean \
    research/T11/axioms_flow_conversion.lean
<no output>
```

Thus no existing Lean module was modified, and there are no forbidden proof
tokens, heartbeat overrides, or anonymous instances.  The only modified
pre-existing file is the split record, with the requested one-line appended
status (`research/T11/T11_SPLIT.md:44`).

## 3. Gaps

There is no proof or statement gap in U1.  The report and attempts file make no
"not in the tree" claim:

```text
$ rg -n -i 'not in (the )?tree|missing lemma|no .* in (the )?tree|absent from (the )?tree' \
    research/T11/REPORT_308.md research/T11/ATTEMPTS_FLOW_CONVERSION.md
<no output>
```

Accordingly the whole-Section4 missing-lemma grep condition has no instance to
audit.  As an additional check on the only deferred helper, a whole-tree search
for a `maximalLifespanT`/Paper-1 `lifespan` equality found none; the sole
`lifespan_eq` hit is the unrelated insertion theorem at
`formalization/NSFormalization/Paper1/PeriodicLifespan.lean:106-112`.  Deferral
to U15 is therefore both binding and honest.

The required substantive negative test flips the viscosity sign in the left
residual (`research/T11/probes/rev308_residual_sign_mutation.lean:11-17`).  It
fails for the expected reason, rather than because an argument was removed:

```text
../research/T11/probes/rev308_residual_sign_mutation.lean:17:2: error: Type mismatch
  source_residual_eq_navierStokesResidual ν u p t x
has type
  Source.residual ν u p t x = NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x
but is expected to have type
  Source.residual (-ν) u p t x = NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x
```

## 4. Commands and results

Environment for every Lean/Lake command: `. scripts/lean-env.sh` (or
`. ../scripts/lean-env.sh` from `verification/`) and
`LEAN_NUM_THREADS=6`; all `lake` commands were run from `verification/`.

### Named module build

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.FlowConversion
⚠ [8778/9285] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
[pre-existing dependency replay warnings omitted]
⚠ [9955/9956] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.
Build completed successfully (9956 jobs).
```

Exit status 0.  The build replayed existing upstream warnings, but emitted no
diagnostic from `FlowConversion.lean`; the direct module check below is exactly
silent as required.

### Direct module and conformance checks

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/FlowConversion.lean
<no output; exit 0>

$ LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/flow_conversion_roundtrip.lean
<no output; exit 0>
```

### Axiom audit

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_flow_conversion.lean
'NSFormalization.Section3.T11.source_residual_eq_navierStokesResidual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.isPeriodicOn_iff_unitSpatialPeriodsOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.toFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.ofFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.toFlow_velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.toFlow_pressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.ofFlow_velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.ofFlow_pressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.toFlow_ofFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.ofFlow_toFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.memForceT_to_isSmoothPeriodicForce' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit status 0.  Every declaration is exactly
`[propext, Classical.choice, Quot.sound]`.

### Repository check

`make check` exited 0.  Its JSON closure listing is very large; exact first and
last 20 lines are reproduced here, in accordance with the review-output size
rule:

```text
$ LEAN_NUM_THREADS=6 make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 561,
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
[middle omitted by reviewer]
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
Ran 13 tests in 0.052s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The reported `BoundaryCorollary.lean` token is the repository's known copied
umbrella finding, not in this lane's import closure or diff; `make check` still
returns success.  Because the lane did not touch `verification/`, the brief's
conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates were
not applicable.
