# Lane 489-MAINT-t22-defprop-warning — MAINT: silence the only Section 3 warning (`T22/Assembly.lean:24 boundedDomainNorm` is a `Prop`-valued `def`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) maintenance worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/489-MAINT-t22-defprop-warning` (git branch `erenup/489-MAINT-t22-defprop-warning`, = `origin/erenup/integration-section3`, 55 contracts). Read `CLAUDE.md`, `logs/SECTION3_BUILD_20260919i.md` §3 (the warning text), `formalization/NSFormalization/Section3/T22/Assembly.lean:20-30`, and every consumer of `boundedDomainNorm` (`grep -rn 'boundedDomainNorm' formalization verification research`).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- **Minimal change, no semantic change**: either turn `def boundedDomainNorm : BoundedDomainNormAPI` into `theorem` (preferred if every consumer only uses it as a proof term — check `Bindings/BoundedDomainNorm.lean` and any `#print axioms`/probe files) or, if some consumer needs it as a `def` (e.g. projections in `rfl` bridges), add `set_option linter.defProp false` scoped to that declaration (`set_option linter.defProp false in`). No other edits.
- Registered `Contracts/V1/*` and `Tests/*` untouched. All declarations keep exactly `[propext, Classical.choice, Quot.sound]`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.Assembly` with **zero warnings from that module** (show the command output), `make check`, `make test`, `make test-mutations`, and re-elaborate every research probe that mentions `boundedDomainNorm` (`lake env lean` on each, zero output).

## Report
Commit on your branch; end with four parts (what changed / files / gaps / commands and results). Also write it to `research/MAINT/REPORT_489.md`.
