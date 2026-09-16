# Lane 261-R46-contract-v1 — register Proposition 4.6 (prop:Renergy, R46) as the 34th contract `R46.completed_density` (V1), instantiating lane 259's assembly with lane 255's realization

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/261-R46-contract-v1` (git branch `erenup/261-R46-contract-v1`, based on lane 259's branch (merged with integration) = everything landed +
`verification/Bindings/CompletedClosure.lean` (`completedHomogeneousDensity_of_realization`, `strongTrajectoryClosure_of_realization`, each `(hreal : CompactHomogeneousRealization) → <Spec field>`) and lane 256's `Bindings/CompletedSobolevDensity.lean` (`completedSobolevDensity`, on integration);
on integration: lane 255's proof of `CompactHomogeneousRealization` (grep `compactHomogeneousRealization` in `Bindings/ScalingHomogeneous*.lean` / `Section4/I03/PathMeasurability.lean`).
Read `CLAUDE.md` (contract import rules; the `ClassicalSolutionR` structure exception and the `maximalPartial_maximalLifespanR_eq` bridge; frozen V1/Tests; `ensure_ascii=False`),
`research/R46/Spec.lean` (the contract must be `REnergyAPI` token for token; registry-conventional names allowed), `research/R46/COMPARISON.md`, `REPORT_256.md`, `REPORT_259.md`, `REPORT_255.md`,
and the registration templates lane 249 (`Contracts/V1/MainThresholds.lean` + Bindings/Tests + registry entry, `research/R41/REPORT_249.md`) and lane 231.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*`/`Tests/*`; additions only in `contracts.json`/`work_items.json`; new files only (258's files are unmerged — do not edit).
- **Statement fidelity:** the contract = `research/R47/Spec.lean` verbatim (the `forceSobolevENorm 1 0` spelling as in the R46 spec — note the R47 spec uses `mixedLebesgueENorm 1 2` for the same term; record this in COMPARISON as an owner question, do not change either spec). If a field cannot be bound as stated, stop and report; do not weaken.

## Deliverables
1. `verification/Contracts/V1/CompletedDensity.lean` (`CompletedDensityAPI` = `REnergyAPI`), importing `Contracts.V1.Data` (+ `InsertionFamily` if the spec needs it).
2. `verification/Bindings/CompletedDensity.lean`: witness `{ completedSobolevDensity := completedSobolevDensity, completedHomogeneousDensity := completedHomogeneousDensity_of_realization compactHomogeneousRealization, strongTrajectoryClosure := strongTrajectoryClosure_of_realization compactHomogeneousRealization }` (+ any `rfl` bridges).
3. `verification/Tests/CompletedDensity.lean` (`checkedCompletedDensity`, `TestSupport.checkAxioms`, a conformance `example`).
4. Registry entry `R46.completed_density` (`version: 1`, `parent_task: R46`, honest scope), `work_items.json` + `python3 experiments/tasks.py render`.
5. Records `research/R46/ATTEMPTS_CONTRACT.md`, conformance `research/R46/axioms_contract.lean`, update `research/R46/COMPARISON.md` (registered).

## Gates (paste outputs)
`scripts/gates.sh`; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts` = current + 1, `base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R46/REPORT_261.md`.
