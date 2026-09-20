# Lane 404-MAINT-t16-deprecations — hygiene: remove the three `if_pos`/`if_neg` deprecation warnings in `Section3/T16/Assembly.lean`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) maintenance worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/404-MAINT-t16-deprecations` (git branch `erenup/404-MAINT-t16-deprecations`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md` and `logs/SECTION3_BUILD_20260918e.md` (the warning block: `Section3/T16/Assembly.lean:327:12 if_neg deprecated: Use ite_eq_right`, `:332:11 if_pos deprecated: Use
ite_eq_left`, `:362:11 if_pos deprecated: Use ite_eq_left`).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- **Lead-approved exception**: you may edit the existing module `formalization/NSFormalization/Section3/T16/Assembly.lean`, but ONLY the three proof terms/tactic steps that trigger the
  warnings. No statement changes, no new declarations, no other files under `formalization/`. No `sorry`/`admit`/`axiom`/`native_decide`/`maxHeartbeats`.
- Do not touch `Paper1/`, `Source/` or Section 4 files (their deprecations are out of scope).

## Goal
Replace the deprecated lemma uses with the pin's replacements (`ite_eq_right`/`ite_eq_left`, or an equivalent `if_pos h ▸`-free `simp only [h, ↓reduceIte]` / `rw [if_pos h]` alternative that
compiles warning-free — check the exact signature of `ite_eq_left`/`ite_eq_right` in this Mathlib with `#check`), so that `lake env lean` on `Assembly.lean` prints **nothing**.
Then verify nothing downstream changed: `grep -rln "Section3.T16.Assembly" formalization verification` and `lake build` every module that imports it (and the contract tests:
`scripts/gates.sh` from the worktree root → `make check`, `make test`, `make test-mutations`), plus `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
(`registered_contracts: 42`, `base_compatibility_checked: true`). Print `#print axioms` for the three affected declarations (standard three only).

## Report
Commit on your branch (`[404-MAINT] Replace deprecated if_pos/if_neg in T16/Assembly.lean`); write `research/MAINT/REPORT_404.md` with four parts (what changed — the three exact
lines before/after / files / any residual warnings / commands and results) and end your message with the same.
