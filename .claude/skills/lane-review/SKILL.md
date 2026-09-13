---
name: lane-review
description: Brief an opus reviewer for a finished lane (light, strict, runs the Lean) and process the verdict.
---
Reviewer = `general-purpose` agent, `model: opus`, one per finished lane, may write exactly one file `research/<ID>/REVIEW*.md`.

Brief must contain: the worktree path (read/build only, no git, no cd to root or other worktrees); `bash scripts/lean-install.sh` then `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake only from `verification/`, one lake at a time; and four checks:
1. Compiles: the exact build/typecheck commands; `#print axioms` = `propext, Classical.choice, Quot.sound`; grep `sorry|admit|axiom|native_decide`; `make check` (contract lanes: `scripts/gates.sh` incl. mutations and `check_contracts.py --base-ref origin/erenup/integration`).
2. Statement fidelity: field by field against the named paper lines and `Contracts/V1/Data.lean`; ask "could a wrong implementation satisfy this?" (quantifier order, constants chosen after the datum, missing positivity/lifespan guards, `Ioo` vs `Ico`, `ℝ≥0∞` vs `ℝ`). Local restatements of contract definitions: token-for-token diff.
3. Consistency with registered contracts and sibling specs (no duplicated fields; imports of registered contracts instead of mirrors).
4. Honesty of ATTEMPTS/COMPARISON: open three cited declarations at the cited lines.
Output: verdict ACCEPT / ACCEPT-WITH-NOTES / REJECT, numbered findings (severity, field, fix), commands with results. Reviewer never fixes code.

Lead afterwards: commit the review file on the lane branch, add a CSV row (`kind=reviewer`), then either merge (`/lane-merge`) or resume the *original worker* with SendMessage listing the findings to fix (cheaper than a fresh agent); REJECT → record the negative example in `research/<ID>/ATTEMPTS*.md` and re-plan.
