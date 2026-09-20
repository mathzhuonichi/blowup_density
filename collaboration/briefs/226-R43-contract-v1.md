# Lane 226-R43-contract-v1 — register Proposition 4.3 (R43, `RCritical1API`: `universal` + `inhomogeneousAtZero`) as the 30th contract `R43.critical_regularity` (V1)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/226-R43-contract-v1` (git branch `erenup/226-R43-contract-v1`, based on lane 225's branch `erenup/225-R43-universal` = `origin/erenup/integration`
+ `Section4/R43/Universal.lean` (`universal_of_memForceR`) — with `Section4/R43/Endpoint.lean` (`inhomogeneousAtZero_of_memForceR`, `criticalConst`, `criticalConst_pos`) already on integration).
Read `CLAUDE.md` (contract import rules: `Contracts/*` import only `Mathlib`/`Lean`/`Init`/`Contracts.*` + the whitelist in `experiments/check_contracts.py`; restated definitions bridged
by `rfl` in `Bindings/`; the **structure exception** for `ClassicalSolutionR`: the local restatement in `Section4/A02/Restrict.lean` §0 is a different inductive type, so
lifespan-dependent statements are bridged through the existing maximal-lifespan equality — grep `maximalLifespanR` in `verification/Bindings/*.lean` for the lemma the A02 V2
binding uses; `ensure_ascii=False, indent=2`; frozen V1/Tests files must not be modified), `collaboration/HANDOFF.md` §0, the top 40 lines of `logs/LESSONS.md`, then the spec
`research/R43/Spec.lean` (`RCritical1API` `:169-247` with its docstrings — the contract must be **this structure token for token**, with the local `dotHomogeneousENorm` replaced by the
registered `Contracts.V1.HomogeneousNorm.dotHomogeneousENorm` (import it; `research/A05/REVIEW_165-A05-critical-l3.md` §"canonical norm: rfl" confirms `rfl`)), `research/R43/COMPARISON.md`,
`research/R43/COMPARISON_UNIVERSAL.md`, `research/R43/REPORT_223.md`, `REPORT_225.md`, the audits `research/R43/axioms_endpoint.lean` and `axioms_universal.lean` (their "conformance in
`Contracts.V1.Data` vocabulary" theorems are exactly the binding proofs you need — reuse them), and the most recent registration lane as the template: lane 181
(`verification/Contracts/V2/GradientL6.lean`, `Bindings/GradientL6V2.lean`, `Tests/GradientL6V2.lean`, registry entry `A05.gradient_l6_v2`, `research/A05/REPORT_181.md`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*` or `Tests/*`; additions only in `contracts.json`/`work_items.json`.
- **Statement fidelity:** the contract structure = `RCritical1API` verbatim (field names, binder order, norms, `c` as a structure field with `0 < c`), docstrings citing
  `04-whole-space.tex:82-89`. No re-cut. If any spec field cannot be bound as stated, stop and report the exact mismatch instead of weakening it.

## Deliverables
1. `verification/Contracts/V1/CriticalRegularity.lean`: `structure CriticalRegularityAPI` (= `RCritical1API`, name per the registry's convention — check `contracts.json` names) importing
   `Contracts.V1.Data` and `Contracts.V1.HomogeneousNorm`.
2. `verification/Bindings/CriticalRegularity.lean`: the witness `{ c := R43.criticalConst, c_pos := …, universal := …, inhomogeneousAtZero := … }` from `Section4/R43/Universal.lean`
   and `Endpoint.lean`, with the bridges (`rfl` for the norms; the maximal-lifespan bridge for the conclusion; force/initial classes by `rfl`) — copy the audit files' conformance proofs.
3. `verification/Tests/CriticalRegularity.lean` (`checkedCriticalRegularity`, `run_cmd TestSupport.checkAxioms`, a conformance `example` restating both fields against `Spec.lean`).
4. Registry entry `R43.critical_regularity` (`version: 1`, `parent_task: R43`, honest scope: both clauses of Prop. 4.3 with the explicit constant; note the constant's value), additions only;
   `work_items.json` + `python3 experiments/tasks.py render`.
5. Records `research/R43/ATTEMPTS_CONTRACT.md`, conformance `research/R43/axioms_contract.lean`; update `research/R43/COMPARISON.md` → registered V1 (new companion file if the rule
   "no edits to existing files" is in force for records — it is not: records may be edited; Lean modules may not).

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root (`make check`, `make test`, `make test-mutations`); `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0,
`registered_contracts: 30`, `base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R43/REPORT_226.md`.
