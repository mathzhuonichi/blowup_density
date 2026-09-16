# Lane 249-R41-contract-v1 — register Theorem 4.1 (R41, `RMainAPI`) as the 32nd contract `R41.main_thresholds` (V1), binding the four fields to lanes 232/233/235

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/249-R41-contract-v1` (git branch `erenup/249-R41-contract-v1`, based on lane 248's branch `erenup/248-SPEC-r41-spec` = `origin/erenup/integration`
+ `research/R41/Spec.lean` (the reconciled `RMainAPI` — **the contract must be this structure token for token**, registry-conventional name allowed) + `research/R41/COMPARISON.md` (§"Binding plan":
exactly which landed theorem binds each field and the adaptation needed) + `research/R41/RECONCILIATION.md`). Read `CLAUDE.md` (contract import rules: `Contracts/*` import only `Mathlib`/`Contracts.*`
+ whitelist; the `ClassicalSolutionR` structure exception and the `Bindings.maximalPartial_maximalLifespanR_eq` bridge; frozen V1/Tests; `ensure_ascii=False`), `collaboration/HANDOFF.md` §0,
the top 40 lines of `logs/LESSONS.md`, the suppliers: `verification/Bindings/DensityFromInsertion.lean` (lane 235: `breakdownDenseR_of_subcritical`, `breakdownDenseR_zero_of_subcritical` — already
in `Contracts.V1.Data` vocabulary), `formalization/NSFormalization/Section4/R41/NonDensity.lean` (lane 232: `not_breakdownDenseR_zero_of_q` with real `q` and the local `rMainThresholds`; its audit
`research/R41D/axioms_nondensity.lean` shows the `Contracts.V1.Data`-vocabulary bridge), `verification/Bindings/InsertionFromData.lean` (lane 233: `insertionLifespanV2_of_data`,
`insertionFromData_lifespan`, `insertionFromData_forceConvergence`; **import caveat**: not together with `Bindings.Packet`), `Contracts/V1/InsertionFamily.lean` (`history`, `energyRate`,
`forceConvergence`, `velocityDifference_*`), `Contracts/V2/InsertionLifespan.lean` (`solution`, `lifespan`), `Bindings/InsertionLifespan.lean` (`memForceR_force`), `Contracts/V1/Data.lean` §5
(`energyENorm`), and the registration templates: lane 231 (`Contracts/V1/CriticalFiniteHorizon.lean`, `Bindings/CriticalFiniteHorizon.lean`, `Tests/CriticalFiniteHorizon.lean`, registry entry,
`research/R44/REPORT_231.md`) and lane 226.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*` or `Tests/*`; additions only in `contracts.json`/`work_items.json`. New files only.
- **Statement fidelity:** the contract = `research/R41/Spec.lean`'s `RMainAPI` verbatim. If a field cannot be bound as stated (most likely the rider's `E_T` convergence if only the rate
  estimate `energyRate` is registered, or the history window), do NOT weaken the contract: register the three bindable fields in a **partial** structure `MainThresholdsPartialAPI` (as
  `A02.maximal_partial`/`A01.regularity_partial` did), name the missing field in the registry scope, and report the exact gap with the supplier that owes it.

## Deliverables
1. `verification/Contracts/V1/MainThresholds.lean` (`MainThresholdsAPI` = `RMainAPI`), importing `Contracts.V1.Data` (+ `Thresholds` if the docstrings cite it).
2. `verification/Bindings/MainThresholds.lean`: the witness; bridges (`rfl` for classes/norms; `maximalPartial_maximalLifespanR_eq` for lifespan statements; the real-`q` ↔ `ℝ≥0∞`-`q`
   adaptation for lane 232's theorem by cases `q = 1`/`q = 2`); the rider from ONE R42 record per reference (do not call 233 separately per conjunct — see `COMPARISON.md` §"Binding plan").
3. `verification/Tests/MainThresholds.lean` (`checkedMainThresholds`, `TestSupport.checkAxioms`, conformance `example`s restating the four fields against `Spec.lean`).
4. Registry entry `R41.main_thresholds` (`version: 1`, `parent_task: R41`, honest scope: Theorem 4.1 for `Y = F_R`, all four clauses — or the partial variant), `work_items.json` + `tasks.py render`.
5. Records `research/R41/ATTEMPTS_CONTRACT.md`, conformance `research/R41/axioms_contract.lean`, update `research/R41/COMPARISON.md` (registered).

## Gates (paste outputs)
`scripts/gates.sh` (`make check`, `make test`, `make test-mutations`); `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts: 32`,
`base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R41/REPORT_249.md`.
