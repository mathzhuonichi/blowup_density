ACCEPT

## 1. What the lane claims

The worker claims that `R46.completed_density` version 1 registers all three
fields of `research/R46/Spec.lean`'s `REnergyAPI`, with only the structure name
changed to `CompletedDensityAPI` (`research/R46/REPORT_261.md:5-11`).  It also
claims that the first force term remains `forceSobolevENorm 1 0`, that the final
witness is unconditional, and that the checkout has 33 rather than 34 contracts
because the concurrent R47 registration has not landed
(`research/R46/REPORT_261.md:13-22`, `research/R46/REPORT_261.md:47-57`).

Those claims are accurate.  The authoritative proposition fixes admissible
`a`, positive `ν,T`, completed inhomogeneous density below `s_q`, completed
homogeneous density at order `-1`, and simultaneous energy plus three-force-norm
convergence (`paper/sections/04-whole-space.tex:218-228`).  Its referenced local
insertion theorem supplies the regular reference through `T+δ`, exact lifespan,
force membership, and one shared family (`paper/sections/04-whole-space.tex:31-42`).
The contract expresses exactly those obligations at
`verification/Contracts/V1/CompletedDensity.lean:39-46`, `:60-65`, and
`:87-112`.  A mechanical comparison of the complete structure block, after the
single name substitution, returned:

```text
structure_byte_match: True
```

The brief's one reference to “`research/R47/Spec.lean` verbatim” is an evident
path typo: the title, requested `REnergyAPI`, deliverable, norm warning, paper
proposition, and all other brief instructions identify R46.  Following R47
literally would instead register Theorem 4.7 and contradict the requested
deliverable.  The lane followed the coherent R46 requirement.

## 2. What is in Lean

The contract imports only `Contracts.V1.InsertionFamily`
(`verification/Contracts/V1/CompletedDensity.lean:1`) and contains the three
Spec fields without extra premises.  The density predicates quantify over every
finite completed datum and every positive `ENNReal` radius and require an actual
approximating force (`verification/Contracts/V1/Data.lean:732-753`); no
`.toReal` occurs in any conclusion and the norm definition fails safely to `⊤`
when no measurable realization exists (`verification/Contracts/V1/Data.lean:215-228`).

The implementation statements agree exactly with the fields:

- `completedSobolevDensity` has the field's full binder order and conclusion
  (`verification/Bindings/CompletedSobolevDensity.lean:25-34`).
- `strongTrajectoryClosure_of_realization` has the full reference pins,
  per-scale membership/lifespan/solution clauses, and both limits
  (`verification/Bindings/CompletedClosure.lean:121-148`).
- `completedHomogeneousDensity_of_realization` has precisely the homogeneous
  field body (`verification/Bindings/CompletedClosure.lean:196-203`).
- The two conditional fields have the single named
  `CompactHomogeneousRealization` input.  That input is a concrete strong
  measurability proposition (`verification/Bindings/ScalingHomogeneous.lean:24-31`)
  and is proved unconditionally
  (`verification/Bindings/ScalingHomogeneousClosed.lean:26-30`).
- `completedDensity` is the literal three-field assembly and discharges both
  conditional inputs with that theorem
  (`verification/Bindings/CompletedDensity.lean:13-20`).

Thus the registered theorem has no residual analytic hypothesis.  The
`a ∈ initialClassR` premise in the closure theorem is not used by the assembly
proof (`verification/Bindings/CompletedClosure.lean:149`), but it is not a
vacuity device: it is required by the paper's fixed-data statement, and the
zero datum is a concrete member used by the passing non-vacuity probe
(`research/R46/probes/rev261_nonvacuity.lean:19-24`).  Likewise the scale range
is nonempty because `InsertionFamilyAPI.eps_pos` states `0 < A.ε₀`
(`verification/Contracts/V1/InsertionFamily.lean:154-164`).  The probe chooses
`ε = A.ε₀` and obtains an actual registered force, exact lifespan, and classical
solution (`research/R46/probes/rev261_nonvacuity.lean:12-26`).

The test exposes the complete witness, checks its transitive axioms, and gives a
conformance example for every field (`verification/Tests/CompletedDensity.lean:15-69`).
The audit prints axioms for the realization, all three suppliers, final binding,
test witness, and final conformance theorem
(`research/R46/axioms_contract.lean:10-15`, `:27-32`).  The registry entry and
its scope are honest (`verification/contracts.json:357-365`), and the work item
lists the same contract (`collaboration/work_items.json:236-243`).

## 3. Gaps, hygiene, and negative checks

There is no blocking mathematical or registration gap.  The retained owner
question is real but outside this R46 contract: `forceSobolevENorm` is an
infimum over Sobolev datum paths (`verification/Contracts/V1/Data.lean:225-228`),
whereas `mixedLebesgueENorm` is an infimum over `L²` slice paths
(`verification/Contracts/V1/Data.lean:242-254`).  The required whole-tree search

```text
grep -rn "mixedLebesgueENorm\|forceSobolevENorm" formalization/NSFormalization/Section4
```

found the mixed-norm construction only in
`formalization/NSFormalization/Section4/I02/Mixed.lean:12-25` and
`formalization/NSFormalization/Section4/I03/Mixed.lean:21-30`, and Sobolev-norm
results in separate files; no Section4 file contains both exact names and no
bridge theorem was found.  The report's narrower claim that the carriers are
not definitionally equal was reproduced:

```text
exit_code=1
../research/R46/probes/rev261_norm_not_rfl.lean:9:2: error: Tactic `rfl` failed: The left-hand side
  forceSobolevENorm 1 0 f
is not definitionally equal to the right-hand side
  mixedLebesgueENorm 1 2 f

f : SpaceTimeField
⊢ forceSobolevENorm 1 0 f = mixedLebesgueENorm 1 2 f
```

The required substantive mutation changes the completed homogeneous order from
`-1` to `0` (`research/R46/probes/rev261_mutation.lean:8-16`).  The existing
proof fails for exactly that changed constant, rather than from a dropped
argument:

```text
exit_code=1
../research/R46/probes/rev261_mutation.lean:16:2: error: Type mismatch
  completedDensity.completedHomogeneousDensity
has type
  ∀ a ∈ initialClassR,
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T → CompletedDenseHomogeneous 2 (-1) (breakdownSetIn forceClassCompact ν a T)
but is expected to have type
  ∀ a ∈ initialClassR,
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T → CompletedDenseHomogeneous 2 0 (breakdownSetIn forceClassCompact ν a T)
```

The matching positive probe (`research/R46/probes/rev261_nonvacuity.lean:12-26`)
exited 0 with no output.  Targeted searches found no code occurrence of
`sorry`, `admit`, `axiom`, or `native_decide` in the new Lean deliverables, and
no `maxHeartbeats` in the lane diff.  `git diff --name-only
origin/erenup/integration...HEAD` listed only the lane's records, registry
updates, and three new Lean modules; `git diff --diff-filter=M --name-only
origin/erenup/integration...HEAD -- '*.lean'` produced no output.  Thus no
existing Lean module, frozen contract, or test was modified.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake from `verification/` only.

Focused binding build:

```text
$ LEAN_NUM_THREADS=6 lake build Bindings.CompletedDensity --log-level=error
Build completed successfully (10637 jobs).
```

Direct elaboration produced exactly zero output:

```text
$ LEAN_NUM_THREADS=6 lake env lean Bindings/CompletedDensity.lean
```

The test target exited 0.  Its lane-specific tail was:

```text
ℹ [10639/10639] Replayed Tests.CompletedDensity
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
Build completed successfully (10639 jobs).
```

The complete axiom-file output was:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/R46/axioms_contract.lean
'NSFormalization.Section4.I03.compactHomogeneousRealization' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.completedSobolevDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.completedHomogeneousDensity_of_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.strongTrajectoryClosure_of_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.completedDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCompletedDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'completedDensityContractConformance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The unfiltered `make check` exited 0.  Its generated closure map is very large;
this is the exact output of a second replay filtered only to command/result
lines under `pipefail`:

```text
python3 experiments/check_formalization_plan.py --check
  "task_count": 30,
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
  "registered_contracts": 33,
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
python3 experiments/test_contract_policy.py
Ran 13 tests in 0.050s
OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The full unfiltered `scripts/gates.sh` run exited 0.  This is the exact concise
replay output, again filtered only after the gate under `pipefail`:

```text
== make check
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
```

The separately required base-ref check exited 0; its requested fields were:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
  "registered_contracts": 33,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
```

The registry diff is addition-only:

```text
$ git diff --stat origin/erenup/integration...HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
$ git diff --numstat origin/erenup/integration...HEAD -- verification/contracts.json
11	0	verification/contracts.json
```

Because the implementation is committed, the brief's worktree-only command
`git diff --stat verification/contracts.json` now exits 0 with no output.
`git diff --check origin/erenup/integration...HEAD` also exits 0 with no output.
