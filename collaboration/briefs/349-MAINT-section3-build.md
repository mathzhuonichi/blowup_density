# Lane 349-MAINT-section3-build — full compile check of Section 3 on the integration branch after the #313–#316 merge batch (+ ledger fix: record `T01.torus_data` under T10)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) build-verification worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/349-MAINT-section3-build` (git branch `erenup/349-MAINT-section3-build`, based on
`origin/erenup/integration-section3` after the merges #313 (`Section3/T11/Assembly.lean` + contract `T01.torus_local_theory`, 39 contracts),
#314 (`T11/ClassicalRegularity.lean`), #315 (`T12/TameProduct.lean`), #316 (`T12/FourierEmbeddings.lean`)). Read `CLAUDE.md` and the previous
report **`logs/SECTION3_BUILD_20260918.md`** (reproduce its structure and tables exactly; it is the template).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6` (the toolchain is already installed here).
- **Do not fix anything.** This is a read-only check of the Lean tree: if a module fails, record the exact error text and the module,
  do not edit `.lean` files. The only tracked edits allowed are the report file and the ledger fix in deliverable 2.
- Report facts only: exit codes, counts, wall time, exact error/warning lines. No summaries that are not backed by a command output.

## Deliverable 1 — `logs/SECTION3_BUILD_20260918b.md` (same sections as the template)
1. Environment table (commit checked = `git rev-parse HEAD`, toolchain, threads).
2. Module inventory: `find formalization/NSFormalization/Section3 -name '*.lean' | sort` (expect 40: T10 7, T11 27, T12 4, T13 1 — count them,
   do not trust this expectation) and per-directory counts.
3. **Full rebuild of every Section 3 module in one `lake build` command**: first delete only the Section 3 build products
   (`formalization/.lake/build/lib/lean/NSFormalization/Section3/` and `…/ir/NSFormalization/Section3/`), then
   `cd verification && time LEAN_NUM_THREADS=6 lake build <all Section 3 module names>` with output to `tmp/section3_build.log`
   (`tmp/` is gitignored). Record exit code, wall time, `grep -c 'error'`, Built/Replayed counts for Section 3 modules, warning lines and
   `grep -c 'warning: NSFormalization/Section3/'` (expect 0 — verify), `.olean` count on disk, `grep -rn sorry formalization/NSFormalization/Section3`.
4. Gates from the worktree root: `make check`, `make test` (expect all 39 contracts `checked; standard logical axioms only` — record the
   actual count), `make test-mutations`, `python3 experiments/check_contracts.py --base-ref main` (record `registered_contracts` and
   `base_compatibility_checked`).
5. Probe + axioms scan: every `research/T1*/**/*_closes.lean`, `research/T1*/axioms_*.lean`, `research/T1*/probes/api_on_canonical.lean`,
   and `research/T11/probes/assembly_closes.lean`, each with `cd verification && lake env lean ../<file>` (4-way parallel, `LEAN_NUM_THREADS=2`
   each); table of pass/fail with the number of files; every failing file with its first error line. Axioms lines must all be
   `[propext, Classical.choice, Quot.sound]` — grep for any other axiom name and report the count (expect 0).
6. Conclusion section: one paragraph, facts only; a list of anything that is not green.

## Deliverable 2 — ledger fix
`collaboration/work_items.json`: the T10 item lists no registered contract although `T01.torus_data` is registered (`verification/contracts.json`,
registered by lane 275/#275 via PR #275 — check the registry entry and cite it). Add `T01.torus_data` to T10's contracts field in the same shape
the T11 item uses for `T01.torus_local_theory` (added by lane 340), then `python3 experiments/tasks.py render` and confirm `make check` passes
(`check_work_queue` consistent). Do not touch any other item. Commit as a separate commit from the report.

## Report
Commit on your branch (two commits: ledger fix; build report). End with four parts (what was checked / what is in the tree now (counts) /
what is not green (exact text) / commands run and results). Also write it to `research/MAINT/REPORT_349.md`.
