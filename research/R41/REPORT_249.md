# Lane 249 — R41 main thresholds V1

## 1. The theorem registered

Registered Theorem 4.1 (`thm:Rmain`, `04-whole-space.tex:7-14`) for `Y = F_R`
as the 32nd contract, `R41.main_thresholds`, version 1. All four fields of the
reconciled `research/R41/Spec.lean` are retained: fixed-initial density,
zero-initial density iff subcritical, the two numerical thresholds, and the
regular-reference rider with one shared family, exact lifespan, unchanged
history, force convergence and energy convergence. A byte comparison of the
complete structure body (including comments) passes after replacing only
`RMainAPI` with `MainThresholdsAPI`.

## 2. What Lean now contains

- `verification/Contracts/V1/MainThresholds.lean`: exact four-field API,
  importing only `Contracts.V1.Data`.
- `verification/Bindings/MainThresholds.lean`: `mainThresholds`, explicit
  force-class/norm definitional bridges, lifespan-based breakdown-set bridge,
  real-q/ENNReal-q case split for lane 232, and lane 235 density bindings.
- The rider calls `insertionLifespanV2_of_data` once. Its reference agrees with
  the quantified solution by registered uniqueness. All four pointwise
  properties and both limits use that same record. The positive-ε history
  endpoint is strictly below T. Spatial slice congruence transports both
  energy summands, and an ENNReal squeeze derives the energy limit from R42's
  registered quantitative rate with exponents 1/2 and 3/2.
- `verification/Tests/MainThresholds.lean`: `checkedMainThresholds`, transitive
  axiom check, and four examples restating the Spec field types.
- `research/R41/axioms_contract.lean`: audits the witness and bridges, checks
  non-density at both critical endpoints, and checks density at q=2, s=-1.
- Registry and R41 contract-list additions; task cards regenerated with
  `python3 experiments/tasks.py render`; attempts and comparison recorded.
  Existing Contracts and Tests files are unchanged.

## 3. Gaps and scope

No mathematical field is missing; no partial API or weaker rider was needed.
This registration concerns relative density in F_R, with q in {1,2}; it does
not register the F_c/F_rd corollary or completed-space density.

The requested `research/R41/RECONCILIATION.md` is absent from this checkout.
The existing reconciled Spec and COMPARISON binding plan were followed exactly;
no replacement statement decision was made. The task state and owner were
left unchanged, respecting the requested additions-only ledger update.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`,
and ran Lake in `verification/`. No push, merge or rebase was performed.

`lake build Tests.MainThresholds` exited 0 (final output):

```text
ℹ [10609/10609] Built Tests.MainThresholds (3.2s)
info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
Build completed successfully (10609 jobs).
```

`scripts/gates.sh` exited 0. Output excerpts (large architecture closure JSON
and other contracts' audit lines omitted):

```text
== make check
== make test
info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
== gates OK
```

The mutation suite runs `lake test` with checked subprocess status before its
mutations, so the successful suite also verifies the test command's exit status.

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
exited 0. Output with only the long `closures` mapping omitted:

```json
{
  "registered_contracts": 32,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41/axioms_contract.lean`
exited 0. Complete output:

```text
'BlowupDensity.Bindings.mainThresholds_forceClassR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_forceSobolevENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_breakdownSetR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_BreakdownDenseR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_nonDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_energy_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_energyConvergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedMainThresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Statement fidelity check:

```text
Spec structure byte-for-byte match after name substitution: PASS
```

Requested registry diff:

```text
$ git diff --stat verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` exited 0 with no output. Full gate logs are local ignored
artifacts under `tmp/mainthresholds-*.log`; the relevant outputs are preserved
above. This report and all deliverables are committed on
`erenup/249-R41-contract-v1`.
