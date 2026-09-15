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

## After ACCEPT: simplifier and tester (every merged proof module gets both, as one small follow-up lane)

**Simplifier** (`prover` agent, one module or one lane's modules): statements byte-identical (the conformance `example`s in `research/<ID>/Axioms*.lean` must still typecheck and `#print axioms` stay standard); shorten proofs (`simp`/`omega`/`positivity` where they close goals, drop dead `have`s, drop unneeded `maxHeartbeats`, drop unused imports and `open`s), one docstring per public theorem naming the paper location, delete duplicated restatements in favour of the single canonical local copy, zero warnings from the module's own lines. Deliverable: a diff that builds, plus a 5-line note in `research/<ID>/ATTEMPTS*.md` ("simplified: …; not simplified because: …").

**Tester** (same or a second `prover` run): (1) the conformance file — every spec field the lane claims has an `example` discharged by the theorem, no extra hypotheses; (2) for contracts, `make test-mutations` and `check_contracts.py --base-ref origin/erenup/integration`; (3) a *negative* check: comment out one hypothesis of the main theorem and confirm the proof breaks (records that the hypothesis is load-bearing) — put the result, not the edit, in ATTEMPTS; (4) the module is inside a compiled closure that CI runs (a registered contract's test, or listed by `experiments/build_changed_lean.py`) — if not, say so and add it to the next contract bundle.

Cadence: reviewer before merge (blocking); simplifier + tester after merge, batched per node (e.g. one `NNN-SIMP-A02` lane for all of A02's merged modules), before that node's contract is registered. Never combine simplifier work with new mathematics in one lane.
