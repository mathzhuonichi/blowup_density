# Lane 231-R44-contract-v1 — register Proposition 4.4 (R44, `RCritical2API`) as the 31st contract `R44.critical_finite_horizon` (V1)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/231-R44-contract-v1` (git branch `erenup/231-R44-contract-v1`, based on lane 229's branch `erenup/229-R44-prop44` = `origin/erenup/integration`
+ `Section4/R44/Absorption.lean`, `Section4/R44/Prop44.lean` (`rcritical2_endpoint_unconditional`; "all nine `RCritical2API` field values/proofs are available with `c = theta/20`, `C = 3`" —
read `research/R44/REPORT_229.md` §2 and the audit `research/R44/axioms_prop44.lean`, whose conformance theorems in `Contracts.V1.Data` vocabulary are the binding proofs), `Section4/R41/NonDensityL2.lean`).
Read `CLAUDE.md` (contract import rules; frozen V1/Tests; `ensure_ascii=False`; the `ClassicalSolutionR` structure exception and the `Bindings.maximalPartial_maximalLifespanR_eq` bridge),
`collaboration/HANDOFF.md` §0, the top 40 lines of `logs/LESSONS.md`, the spec `research/R44/Spec.lean:169-230` (`RCritical2API` with docstrings — the contract must be **this structure token
for token**; check every norm is spelled with registered `Contracts.V1.Data`/`HomogeneousNorm` definitions), `research/R44/COMPARISON.md`, `R44_SPLIT.md` (S6 and the ledger), and the
registration template lane 226 (`verification/Contracts/V1/CriticalRegularity.lean`, `Bindings/CriticalRegularity.lean`, `Tests/CriticalRegularity.lean`, registry entry `R43.critical_regularity`,
`research/R43/REPORT_226.md`, `REVIEW_226-*.md`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*` or `Tests/*`; additions only in `contracts.json`/`work_items.json`.
- **Statement fidelity:** the contract structure = `RCritical2API` verbatim (field names, binder order, the radius as a structure field with its positivity and the explicit formula only in the
  binding). If any field cannot be bound as stated, stop and report the exact mismatch; do not weaken.

## Deliverables
1. `verification/Contracts/V1/CriticalFiniteHorizon.lean` (`CriticalFiniteHorizonAPI` = `RCritical2API`), importing `Contracts.V1.Data` (+ `HomogeneousNorm` if needed).
2. `verification/Bindings/CriticalFiniteHorizon.lean`: the witness from `R44.Prop44`/`Endpoint` (`c := theta/20`, `C := 3`, `radius`, `main`, `nonDensityBallZero`, …), `rfl` bridges,
   the maximal-lifespan bridge for lifespan conclusions.
3. `verification/Tests/CriticalFiniteHorizon.lean` (`checkedCriticalFiniteHorizon`, `TestSupport.checkAxioms`, conformance `example`s restating the fields against `Spec.lean`).
4. Registry entry `R44.critical_finite_horizon` (`version: 1`, `parent_task: R44`, honest scope: zero-datum finite-horizon regularity with explicit radius), `work_items.json` + `tasks.py render`.
5. Records `research/R44/ATTEMPTS_CONTRACT.md`, conformance `research/R44/axioms_contract.lean`, update `research/R44/COMPARISON.md` (registered V1).

## Gates (paste outputs)
`scripts/gates.sh`; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts: 31`, `base_compatibility_checked: true`); the axioms file;
`git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R44/REPORT_231.md`.
