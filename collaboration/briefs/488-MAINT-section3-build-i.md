# Lane 488-MAINT-section3-build-i — full compile check of Section 3 on the integration branch after the #438–#451+ merge batch (T23 registered; expect 55 contracts)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) build-verification worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/488-MAINT-section3-build-i` (git branch `erenup/488-MAINT-section3-build-i`, based on
`origin/erenup/integration-section3` after the merges #354–#421: T15 U1–U14(q=1) (`Section3/T15/*`, 16 modules), T17 U1–U12 + contract `T02.correction` (#414), T18 U1–U12 + contract `T03.periodic_insertion` (#420),
T20 U1–U13 + contract `T03.critical_regularity` (#415), T19 canonical `Density.lean` (#421), T22/T24 contracts (#391/#392/#396), T12 `DirDeriv` dedupe). Read `CLAUDE.md` and the previous report
**`logs/SECTION3_BUILD_20260918f.md`** (reproduce its structure and tables exactly; it is the template).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6` (the toolchain is already installed here).
- **Do not fix anything.** This is a read-only check of the Lean tree: if a module fails, record the exact error text and the module,
  do not edit `.lean` files. The only tracked edit allowed is the report file.
- Report facts only: exit codes, counts, wall time, exact error/warning lines. No summaries that are not backed by a command output.

## Deliverable — `logs/SECTION3_BUILD_20260919i.md` (same sections as the template)
1. Environment table (commit checked = `git rev-parse HEAD`, toolchain, threads).
2. Module inventory: `find formalization/NSFormalization/Section3 -name '*.lean' | sort` (expect about 142 — count them, do not trust this expectation) and per-directory counts.
3. **Full rebuild of every Section 3 module in one `lake build` command**: first delete only the Section 3 build products
   (`formalization/.lake/build/lib/lean/NSFormalization/Section3/` and `…/ir/NSFormalization/Section3/`), then
   `cd verification && time LEAN_NUM_THREADS=6 lake build <all Section 3 module names>` with output to `tmp/section3_build.log`
   (`tmp/` is gitignored). Record exit code, wall time, `grep -c 'error'`, Built/Replayed counts for Section 3 modules, warning lines and
   `grep -c 'warning: NSFormalization/Section3/'` (expect 0 — verify), `.olean` count on disk, `grep -rn sorry formalization/NSFormalization/Section3`.
4. Gates from the worktree root: `make check`, `make test` (expect all 55 contracts `checked; standard logical axioms only` — record the
   actual count), `make test-mutations`, `python3 experiments/check_contracts.py --base-ref main` (record `registered_contracts` (expect 55) and
   `base_compatibility_checked`).
5. Probe + axioms scan: every `research/T1*/**/*_closes.lean`, `research/T1*/axioms_*.lean`, `research/T1*/probes/api_on_canonical.lean`,
   and `research/T2*/probes/*.lean`, `research/T2*/axioms_*.lean`, each with `cd verification && lake env lean ../<file>` (4-way parallel, `LEAN_NUM_THREADS=2`
   each); table of pass/fail with the number of files; every failing file with its first error line (reviewer mutation probes `rev*_mutation*.lean` / `*negative*.lean` / `*widen*` / `*_sign_*` are **expected to fail** —
   list them separately as expected failures, do not count them as red). Axioms lines must all be `[propext, Classical.choice, Quot.sound]` — grep for any other axiom name and report the count (expect 0).
6. Conclusion section: one paragraph, facts only; a list of anything that is not green.

## Report
Commit on your branch (one commit: the build report). End with four parts (what was checked / what is in the tree now (counts) /
what is not green (exact text) / commands run and results). Also write it to `research/MAINT/REPORT_488.md`.
