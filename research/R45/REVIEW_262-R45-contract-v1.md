REJECT

## 1. What the lane claims

The worker claims that Corollary 4.5 is registered as `R45.force_classes`, then
describes the four fields `density`, `zeroIff`, `schwartzDensity`, and
`regularReference` (`research/R45/REPORT_262.md:5-16`).  It claims the binding
uses the guarded declarations from lane 257 plus the compact/rapid rider case
split (`research/R45/REPORT_262.md:20-32`), and that no mathematical field or
statement-level gap remains (`research/R45/REPORT_262.md:42-52`).  The registry
entry says the same thing and names the exact binding and test modules
(`verification/contracts.json:357-365`).

The mathematical scope is the right one.  Theorem 4.1 states density below
`s_q = 2/q - 3/2`, the zero-data iff, and the regular-reference rider
(`paper/sections/04-whole-space.tex:7-13`).  Corollary 4.5 replaces the ambient
force class by `F_c` or `F_rd`, adds the Schwartz specialization, and explicitly
says the complete zero classification is retained
(`paper/sections/04-whole-space.tex:194-198`).

## 2. What is in Lean

The Lean content is statement-faithful.

- Mechanical extraction of the two structure blocks, replacing only
  `RClassesAPI` by `ForceClassesAPI`, returned
  `structure_byte_match: True`.  The four contract fields are at
  `verification/Contracts/V1/ForceClasses.lean:36-42`, `:56-62`, `:76-82`, and
  `:102-119`, matching the research spec at `research/R45/Spec.lean:64-70`,
  `:84-90`, `:104-110`, and `:130-147`.
- The final guarded rider is exactly the claimed two-case assembly
  (`verification/Bindings/ForceClasses.lean:22-43`), and the final witness
  assigns the four named suppliers directly (`verification/Bindings/ForceClasses.lean:45-50`).
  The supplier statements exist with the claimed types: guarded density and
  zero iff at `verification/Bindings/RapidClassDensity.lean:227-251`, Schwartz
  density at `:214-223`, compact rider at
  `verification/Bindings/CompactClassRider.lean:29-46`, and rapid rider at
  `verification/Bindings/RapidClassDensity.lean:125-142`.
- The cited tree facts are honest rather than hidden supplier assumptions:
  rapid forces enter `F_R` at
  `formalization/NSFormalization/Section4/R41/ClassFacts.lean:1067-1071`, compact
  corrections preserve rapid decay at `:1162-1169`, and Schwartz data enter
  `initialClassR` at `:1189-1197`.  The insertion supplier requires the genuine
  strict lifespan premise and returns an actual insertion record
  (`verification/Bindings/InsertionFromData.lean:87-110`).
- There is no `.toReal` escape on either approximation norm:
  `forceSobolevENorm` and `energyENorm` are `ℝ≥0∞`-valued
  (`verification/Contracts/V1/Data.lean:215-228`, `:463-476`).  The class guard,
  `q = 1 ∨ q = 2`, `T > 0`, `0 ≤ τ < T`, and both positive radii remain in the
  contract (`verification/Contracts/V1/ForceClasses.lean:37-41`, `:103-119`).
  Thus `⊤.toReal = 0`, an empty energy interval, and an unconstrained exponent
  cannot make the statement vacuous.
- The test module independently restates all four fields
  (`verification/Tests/ForceClasses.lean:18-67`) and checks the final witness's
  transitive axioms (`verification/Tests/ForceClasses.lean:13-16`).
- The reviewer non-vacuity probe uses the genuine zero solution on horizon two,
  positive `T = 1`, and the nondegenerate history interval `[0, 1/2]`; the final
  registered rider produces a force and solution with exact lifespan and both
  strict bounds (`research/R45/probes/rev262_nonvacuity.lean:12-37`).  It
  typechecks with zero output.
- The substantive negative probe widens the density range from
  `s < criticalOrder q.toReal` to `s < criticalOrder q.toReal + 1`
  (`research/R45/probes/rev262_widen_threshold.lean:3-22`).  The registered proof
  is rejected specifically at that changed inequality, not because an argument
  was dropped.

Hygiene is clean for the lane's Lean files.  The forbidden-declaration search
for `sorry`, `admit`, `axiom`, and `native_decide` produced no output, as did the
`maxHeartbeats` search.  The only Lean modules in the lane diff are the three
new files `Contracts/V1/ForceClasses.lean`, `Bindings/ForceClasses.lean`, and
`Tests/ForceClasses.lean`; no existing Lean module is modified.  The contract
imports only `Contracts.V1.Data` (`verification/Contracts/V1/ForceClasses.lean:1`).

## 3. Gaps

The mathematical implementation has no identified gap.  The worker declares no
"not in the tree" mathematical gap (`research/R45/REPORT_262.md:42-50`), so the
requested whole-`Section4` missing-lemma grep is not applicable.

The blocking gap is repository-base compatibility.  During review,
`origin/erenup/integration` advanced from the lane's merge base
`bf6fc86b1e9e05fc68782423981d5957eb290785` to
`ee6660ec1564e5f478f3e96276ec6c96f5a12e54`.  The current base has 34 contracts
and contains the newly stable `verification/Contracts/V1/CompletedDensity.lean`
and `GridObservations.lean`; this lane has neither.  The compatibility checker
intentionally rejects a stable base specification missing from the worktree
(`experiments/check_contracts.py:54-64`).  Consequently both the standalone
required command and the final phase of `scripts/gates.sh` now fail with:

```text
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/262-R45-contract-v1/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/262-R45-contract-v1/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/262-R45-contract-v1/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/CompletedDensity.lean
```

Required fix: synchronize the lane with the current
`origin/erenup/integration`, retain both newly registered contracts and
`R45.force_classes` in the registry/work queue, rerun
`python3 experiments/tasks.py render`, and rerun every gate.  The refreshed
base has 34 contracts, so the successful lane result must report 35 rather than
the now-stale "33rd contract" wording at `research/R45/REPORT_262.md:5-7` and
the `registered_contracts: 33` output at `:90-100`.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
all Lake commands ran from `verification/`.  No fetch, merge, rebase, commit, or
other git state change was made by the reviewer.

`bash scripts/lean-install.sh` exited 0.  It confirmed Lean
`v4.34.0-rc2`, found the cache already installed, and ended with:

```text
== OK
```

`lake build Bindings.ForceClasses` exited 0.  It replayed pre-existing upstream
warnings; there was no diagnostic from `Bindings/ForceClasses.lean`.  Exact
final output:

```text
Build completed successfully (10615 jobs).
```

`lake env lean Bindings/ForceClasses.lean` exited 0 with exactly zero output.

`lake build Tests.ForceClasses` exited 0.  Exact lane-owned tail:

```text
ℹ [10617/10617] Replayed Tests.ForceClasses
info: Tests/ForceClasses.lean:16:0: Contract BlowupDensity.Tests.checkedForceClasses: checked; standard logical axioms only
Build completed successfully (10617 jobs).
```

`lake env lean ../research/R45/axioms_contract.lean` exited 0 with complete
output:

```text
'BlowupDensity.Bindings.density' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.zeroIff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.schwartzDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.regularReference_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.regularReference_rapid' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.regularReference' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.forceClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedForceClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/R45/probes/rev262_nonvacuity.lean` exited 0 with
exactly zero output.

`lake env lean ../research/R45/probes/rev262_widen_threshold.lean` exited 1 with
the expected error:

```text
../research/R45/probes/rev262_widen_threshold.lean:22:2: error: Type mismatch
  checkedForceClasses.density
has type
  ∀ (Y : Set SpaceTimeField),
    Y = forceClassCompact ∨ Y = forceClassRapid →
      ∀ (ν : ℝ),
        0 < ν →
          ∀ (T : ℝ),
            0 < T →
              ∀ (q : ℝ≥0∞),
                q = 1 ∨ q = 2 →
                  ∀ (s : ℝ),
                    ∀ a ∈ initialClassR, s < criticalOrder q.toReal → RelativelyDense q s Y (breakdownSetIn Y ν a T)
but is expected to have type
  ∀ (Y : Set SpaceTimeField),
    Y = forceClassCompact ∨ Y = forceClassRapid →
      ∀ (ν : ℝ),
        0 < ν →
          ∀ (T : ℝ),
            0 < T →
              ∀ (q : ℝ≥0∞),
                q = 1 ∨ q = 2 →
                  ∀ (s : ℝ),
                    ∀ a ∈ initialClassR, s < criticalOrder q.toReal + 1 → RelativelyDense q s Y (breakdownSetIn Y ν a T)
```

`make check` exited 0.  Its architecture JSON is large; exact head and tail:

```text
python3 experiments/check_formalization_plan.py --check
...
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

On the final current-base run, `scripts/gates.sh` exited 1.  Its Lean tests and
mutation suite passed, then the base gate failed.  Exact final output:

```text
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/262-R45-contract-v1/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/262-R45-contract-v1/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/262-R45-contract-v1/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/CompletedDensity.lean
```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
independently exited 1 with the identical traceback above.  The base registry
currently contains 34 contracts; its last two IDs are exactly:

```text
R47.grid_observations
R46.completed_density
```

The brief's literal `git diff --stat verification/contracts.json` produced no
output because the worker changes are committed.  The base-qualified audit
produced:

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check origin/erenup/integration...HEAD` exited 0 with zero output.

