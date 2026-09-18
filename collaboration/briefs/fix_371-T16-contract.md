# Continuation brief for lane 371-T16-contract — fix the codex REJECT (test deliverables) for the registration of `T02.local_potential`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/371-T16-contract` (git branch `erenup/371-T16-contract`; your previous run registered `T02.local_potential` in commits
`a71f12a7` (ledger claim) and `d39f4fd7` (contract)). The codex review returned **REJECT on test deliverables only** ("the core theorem is faithful and all gates pass") —
read `research/T16/REVIEW_371-T16-contract.md` and the reviewer's probes `research/T16/probes/rev371_mutation.lean`, `research/T16/probes/rev371_nonvacuity.lean` (untracked; keep them and
include them in your commit). Then read the original brief `tmp/codex/briefs/371-T16-contract.md` for the ground rules (no edits to frozen `Contracts/V1`/`Tests` other than the
new files of this lane; `Tests/` is `warningAsError`; import only through `Bindings`).

## Fixes (exactly the review's four items)
1. `verification/Tests/LocalPotential.lean`: add an **independent Spec conformance `example`** restating `localPotentialStatement` (and the `LocalPotentialAPI` field list) token-for-token
   against `research/T16/Spec.lean:320-338` / `:145-318`, checked against the contract's declarations (as `Tests/TorusLocalTheory.lean` does for T11).
2. Replace the zero-field test with the reviewer's **verified nonzero constant-field instance** (`rev371_nonvacuity.lean`: `v = fun _ => coordinateVector 0`, `U = 0`, `K = {0}`,
   `x₀`, `r = 1/4`, `T = δ = 1`, via `Bindings.localPotential`) plus the `coordinateVector 0 ≠ 0` witness.
3. `research/T16/REPORT_371.md`: add the **full gate outputs** — run and paste `scripts/gates.sh` from the worktree root with `BASE_REF=origin/erenup/integration-section3`
   (`make check`, `make test`, `make test-mutations`), `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (expect `registered_contracts: 41`,
   `base_compatibility_checked: true`), the axioms file, and `git diff --stat verification/contracts.json`.
4. `research/T16/ATTEMPTS_CONTRACT.md`: correct "pointwise bridges" to "whole-function `rfl` bridges" where the bridges are stated as whole-function equalities.
Append a fix note to the REVIEW file. Commit on your branch (never push/merge/rebase). Report in four parts with the commit hash.
