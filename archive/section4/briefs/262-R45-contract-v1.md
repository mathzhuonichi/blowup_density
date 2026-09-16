# Lane 262-R45-contract-v1 — register Corollary 4.5 (cor:Rclasses, R45) as the 33rd contract `R45.force_classes` (V1): the four fields of `research/R45/Spec.lean` from lanes 252/254/257

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/262-R45-contract-v1` (git branch `erenup/262-R45-contract-v1`, based on `origin/erenup/integration` after lane 257 merged: it contains
`verification/Bindings/CompactClassDensity.lean` (252: `density_compact`, `zeroIff_compact`), `Bindings/CompactClassRider.lean` (254: `regularReference_compact`, `regularReference_of_memForceR`),
`Bindings/RapidClassDensity.lean` (257: `density_rapid`, `zeroIff_rapid`, `regularReference_rapid`, `schwartzDensity`, and the guarded parametric `density`/`zeroIff`)). Read `CLAUDE.md`
(contract import rules; the `ClassicalSolutionR` structure exception and the `maximalPartial_maximalLifespanR_eq` bridge; frozen V1/Tests; `ensure_ascii=False`), `research/R45/Spec.lean`
(the contract must be `RClassesAPI` token for token; registry-conventional structure name allowed), `research/R45/COMPARISON.md`, `RECONCILIATION.md`, `REPORT_252.md`, `REPORT_254.md`,
`REPORT_257.md`, and the registration templates lane 249 (`Contracts/V1/MainThresholds.lean` + Bindings/Tests + registry entry) and lane 231.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*`/`Tests/*`; additions only in `contracts.json`/`work_items.json`; new files only.
- **Statement fidelity:** the contract = `research/R45/Spec.lean` verbatim. If a field cannot be bound as stated, stop and report; do not weaken.

## Deliverables
1. `verification/Contracts/V1/ForceClasses.lean` (`ForceClassesAPI` = `RClassesAPI`), importing `Contracts.V1.Data`.
2. `verification/Bindings/ForceClasses.lean`: witness — `density`/`zeroIff` from 257's guarded theorems (or `Or.elim` of 252/257), `schwartzDensity` from 257, `regularReference` by `Or.elim` of
   254's `regularReference_compact` and 257's `regularReference_rapid` (the guarded combination 257 left to this lane); `rfl` bridges as needed.
3. `verification/Tests/ForceClasses.lean` (`checkedForceClasses`, `TestSupport.checkAxioms`, conformance `example`s restating the four fields).
4. Registry entry `R45.force_classes` (`version: 1`, `parent_task: R45`, honest scope), `work_items.json` + `python3 experiments/tasks.py render`.
5. Records `research/R45/ATTEMPTS_CONTRACT.md`, conformance `research/R45/axioms_contract.lean`, update `research/R45/COMPARISON.md` (registered).

## Gates (paste outputs)
`scripts/gates.sh`; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts` = current + 1, `base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R45/REPORT_262.md`.
