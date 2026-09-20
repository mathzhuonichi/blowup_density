# Lane 471 — T24b Ub7 assembly and `T04.multiple_regions` registration

## 1. What was registered, with the exact statement

`T04.multiple_regions` version 1 registers the torus branch of
`prop:multiple` (`03-torus.tex:697-722`). Its exact existence statement is

```lean
def multipleRegionsStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν) (T : ℝ), 0 < T →
    ∀ (N : ℕ), 0 < N →
      ∀ (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ),
        (∀ j : Fin N, 0 < regionRadius j) →
        (∀ j : Fin N, closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆
          interior fundamentalCube) →
        Pairwise (fun i j : Fin N ↦
          Disjoint (Metric.ball (regionCenter i) (regionRadius i))
            (Metric.ball (regionCenter j) (regionRadius j))) →
        Nonempty (MultipleRegionsAPI P T regionCenter regionRadius)
```

`MultipleRegionsAPI` is the Spec's `Type`-valued 30-field record, indexed by
that packet, horizon, and prescribed balls. In order, its fields are
`T_pos`, `N_pos`, `regionRadius_pos`, `region_interior`, `regions_disjoint`,
`placement`, `placement_time`, `placement_chart`, `scaling`, `ε`,
`eps_admissible`, `eps_time`, `component`, `component_pin`,
`component_support`, `component_force_support`, `assembled_velocity`,
`assembled_velocity_formula`, `assembled_pressure`,
`assembled_pressure_formula`, `assembled_force`, `assembled_force_formula`,
`solution`, `solution_pin`, `force_mem`, `rest`, `region_agreement`,
`region_blowup`, `energy_bound`, and `dissipation_bound`. The last two are
exactly

```lean
(energyEssSupT T assembled_velocity) ^ (2 : ℕ) ≤
  ENNReal.ofReal (P.energyBound ^ 2 * ∑ j : Fin N, ε j)

(energyGradientT T assembled_velocity) ^ (2 : ℕ) =
  ENNReal.ofReal (P.dissipationBound ^ 2 * ∑ j : Fin N, ε j)
```

The canonical raw-field theorem has the same conclusion after all raw packet
clauses. It builds `RegionsData` from those clauses and applies the single
30-field constructor; it does not assume an assembled solution or any Ub field.

## 2. Files and Lean contents

- `formalization/NSFormalization/Section3/T24/MultipleAssembly.lean` defines
  `multipleRegionsAPI` and proves `multipleRegionsStatement_holds`.
- `formalization/NSFormalization/Section3/T24/MultipleRegions.lean` contains
  the authorized lane-468/lane-469 deduplication: it imports
  `MultipleAssembled` and reuses its definitionally identical
  `RegionsData.assembledVelocity`; all Ub5/Ub6 theorem statements are unchanged.
- `verification/Contracts/V1/MultipleRegions.lean` restates the Spec's four
  definitions, 30-field packet-indexed record, and statement over registered
  T10/T13/T14/T15 vocabulary.
- `verification/Bindings/MultipleRegions.lean` has four whole-function `rfl`
  drift guards, two 30-field conversions with `rfl` round trips, the raw packet
  projection bundle, the record constructor, and the statement proof.
- `verification/Tests/MultipleRegions.lean` provides
  `checkedMultipleRegions` and three independent final-field shape checks.
- `research/T24/probes/multiple_nonvacuity.lean` instantiates the registered
  packet at `ν=1`, `T=1`, `N=1`, centre `(1/2,1/2,1/2)`, radius `1/4`, obtains
  the API through the registered universal statement, and reads
  `region_blowup 0`.
- `research/T24/axioms_ub7.lean` audits 22 new declarations; every line is
  exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T24/ATTEMPTS_UB7.md` records the duplicate reconciliation and all
  resolved elaboration diagnostics. `T24_SPLIT.md`, the contract registry,
  T24 work item, and generated task cards are updated.

## 3. Gaps and scope

There is no remaining Ub7 or torus `prop:multiple` proof gap. The paper's
bounded-domain/homogeneous-no-slip branch (`03-torus.tex:698,703,719`) is not
registered: V1 now has a bounded-domain norm layer, but no bounded-domain
solution/no-slip carrier is threaded through T24b. The registry records this as
an explicit omission, not as torus periodicity and not as a placeholder field.

No T18 insertion theorem is consumed, and no density consequence, sharpness,
or optimality statement is claimed.

## 4. Commands and results

All Lake commands ran from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

- Required closure first:
  `lake build NSFormalization.Section3.T24.MultipleAssembled NSFormalization.Section3.T24.MultipleRegions`
  — passed, 10,052 jobs.
- `lake build NSFormalization.Section3.T24.MultipleAssembly` — passed, 10,053
  jobs; final build has no new-module linter warning.
- `lake build Tests.MultipleRegions` — passed; the new line is
  `Contract BlowupDensity.Tests.checkedMultipleRegions: checked; standard logical axioms only`.
- `lake env lean ../research/T24/probes/multiple_nonvacuity.lean` — exit 0,
  zero output.
- `lake env lean ../research/T24/axioms_ub7.lean` — exit 0; all 22 entries have
  exactly the standard three axioms.
- `make check` — passed; 51 registered contracts and 45 work items consistent.
- `make test` — passed; the new checked line prints the standard-axiom result.
- `make test-mutations` — passed: implementation refactor accepted; admitted
  proof, extra axiom, and weakened hypothesis rejected.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
  — passed with `registered_contracts: 51`, base count 50, and
  `base_compatibility_checked: true`.
