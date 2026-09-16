# Lane 260-R47-contract-v1 — register Theorem 4.7 (thm:Rgrid, R47) as the 35th contract `R47.grid_observations` (V1), instantiating lane 258's assembly with lane 255's realization

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/260-R47-contract-v1` (git branch `erenup/260-R47-contract-v1`, based on lane 258's branch (merged with integration) = everything landed +
`verification/Bindings/GridAssembly.lean` (`rGrid_choose_of_realization (hreal : CompactHomogeneousRealization) : <RGridAPI.choose>`, `rGridFamily_of_data`) + `Bindings/GridAssemblyNorms.lean`;
on integration: lane 255's proof of `CompactHomogeneousRealization` (grep `compactHomogeneousRealization` in `Bindings/ScalingHomogeneous*.lean` / `Section4/I03/PathMeasurability.lean`).
Read `CLAUDE.md` (contract import rules; the `ClassicalSolutionR` structure exception and the `maximalPartial_maximalLifespanR_eq` bridge; frozen V1/Tests; `ensure_ascii=False`),
`research/R47/Spec.lean` (the contract must be `RGridFamily` + `RGridAPI` token for token; registry-conventional names allowed), `research/R47/COMPARISON.md`, `REPORT_258.md`, `REPORT_255.md`,
and the registration templates lane 249 (`Contracts/V1/MainThresholds.lean` + Bindings/Tests + registry entry, `research/R41/REPORT_249.md`) and lane 231.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*`/`Tests/*`; additions only in `contracts.json`/`work_items.json`; new files only (258's files are unmerged — do not edit).
- **Statement fidelity:** the contract = `research/R47/Spec.lean` verbatim (the `mixedLebesgueENorm 1 2` spelling as in the spec). If a field cannot be bound as stated, stop and report; do not weaken.

## Deliverables
1. `verification/Contracts/V1/GridObservations.lean` (`GridFamilyAPI`/`GridObservationsAPI` = `RGridFamily`/`RGridAPI`), importing `Contracts.V1.Data` (+ `InsertionFamily` if the spec needs it).
2. `verification/Bindings/GridObservations.lean`: witness `{ choose := rGrid_choose_of_realization compactHomogeneousRealization }` (+ any `rfl` bridges).
3. `verification/Tests/GridObservations.lean` (`checkedGridObservations`, `TestSupport.checkAxioms`, a conformance `example`).
4. Registry entry `R47.grid_observations` (`version: 1`, `parent_task: R47`, honest scope), `work_items.json` + `python3 experiments/tasks.py render`.
5. Records `research/R47/ATTEMPTS_CONTRACT.md`, conformance `research/R47/axioms_contract.lean`, update `research/R47/COMPARISON.md` (registered).

## Gates (paste outputs)
`scripts/gates.sh`; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts` = current + 1, `base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R47/REPORT_260.md`.
