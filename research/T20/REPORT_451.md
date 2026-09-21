# Lane 451 report — T20 U13 assembly and registration

## 1. Theorem proved

`formalization/NSFormalization/Section3/T20/Assembly.lean` defines the complete
canonical 23-field package

```lean
def criticalRegularityT : CriticalRegularityTAPI := { ... }
```

with `c := criticalSmallnessH1`, `C₀ := criticalTrilinearConst`,
`C₁ := h1TrilinearConst`, `CH1 := 2`, and the closed canonical
`Ccriterion`.  Its mathematical fields are the landed U1–U12 theorems;
in particular, U5 is lane 452's `constantTransportCommutesLambda`, and
`yBound` is `yBound_of_le criticalSmallnessH1_le_half`.  Consequently it proves

```lean
theorem criticalRegularityStatement_holds : criticalRegularityStatement :=
  ⟨criticalRegularityT⟩
```

The same module proves genuine non-vacuity at a nonzero spatially constant
force made from a compact positive-time bump.  Its critical size is finite, so
the positive viscosity
`((criticalRho g).toReal + 1) / criticalSmallnessH1` gives strict smallness;
the assembled global-regularity field then gives infinite maximal lifespan.

## 2. Lean contents delivered

- `formalization/NSFormalization/Section3/T20/Assembly.lean` — canonical
  23-field assembly, proposition theorem, and nonzero compact-force witness.
- `verification/Contracts/V1/CriticalRegularityT.lean` — the reconciled T20
  contract, with the `CriticalRegularityTAPI` record copied token-for-token
  from `research/T20/Spec.lean`; already registered T10/T11/T12 vocabulary is
  imported, and only T20-specific notions are restated.
- `verification/Bindings/CriticalRegularityT.lean` — `rfl` drift guards for
  every restated definition, fieldwise `ClassicalSolutionT` transport through
  `Bindings.TorusLocalTheory.ofContract`, and lifespan transport through
  `Bindings.TorusLocalTheory.maximalLifespanT_eq`.
- `verification/Tests/CriticalRegularityT.lean` —
  `checkedCriticalRegularityT`, the axiom check, three explicit Spec-field
  conformance examples, proposition inhabitation, and registered non-vacuity.
- `verification/contracts.json` — additive V1 registration
  `T03.critical_regularity` under parent `T03`, with the actual closed constants
  and contract scope recorded.
- `collaboration/work_items.json`, `collaboration/TASKS.md`, and
  `collaboration/tasks/T20.md` — work item and rendered task-card updates.
- `research/T20/ATTEMPTS_U13.md`, `research/T20/axioms_u13.lean`, and
  `research/T20/T20_SPLIT.md` — development record, transitive audit, and U13
  DONE status.

## 3. Gaps and registration-name collision

There is no mathematical, Lean, non-vacuity, or local-existence gap.  The
nonzero force witness satisfies the actual strict small-data premise and uses
the assembled theorem to obtain infinite lifespan.  No `sorry`, `admit`,
`axiom`, `native_decide`, named proposition input, or placeholder field was
introduced.  Every audited canonical and binding declaration depends exactly
on:

```text
[propext, Classical.choice, Quot.sound]
```

The requested unsuffixed module and declaration names could not be used:
`Contracts/V1/CriticalRegularity.lean`, `Bindings/CriticalRegularity.lean`,
`Tests/CriticalRegularity.lean`, and `checkedCriticalRegularity` already form
the frozen registered whole-space contract `R43.critical_regularity`.  Editing
or replacing them would violate V1 base compatibility.  The new torus contract
therefore uses the additive suffix `T` in its module namespaces and public test
declaration.  The requested registry id remains exactly
`T03.critical_regularity`, and the existing R43 registration is unchanged.

## 4. Commands and results

All Lake work ran from `verification/` through the root gate after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

- `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T20.Assembly Contracts.V1.CriticalRegularityT Bindings.CriticalRegularityT Tests.CriticalRegularityT`
  — exit 0; the build completed successfully (`10675` jobs),
  `checkedCriticalRegularityT` reported standard logical axioms only, all tests
  and mutation checks passed, and the final line was:

  ```text
  == gates OK
  ```

- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
  — exit 0; the base had 46 registered contracts and the result reported:

  ```text
  "registered_contracts": 47
  "base_compatibility_checked": true
  ```

- `LEAN_NUM_THREADS=6 lake env lean ../research/T20/axioms_u13.lean`
  — exit 0; all ten audited declarations printed exactly
  `[propext, Classical.choice, Quot.sound]`.
- `python3 experiments/tasks.py render` — exit 0; regenerated the task index
  and T20 task card.
- `git diff --stat verification/contracts.json` — output:

  ```text
   verification/contracts.json | 11 +++++++++++
   1 file changed, 11 insertions(+)
  ```

- `git diff --check` — exit 0, no output.
