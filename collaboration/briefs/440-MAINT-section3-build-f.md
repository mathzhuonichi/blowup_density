# Lane 440-MAINT-section3-build-f — full compile check of Section 3 on the integration branch after the #339–#353 merge batch

You are a Lean 4 (v4.34.0-rc2 + Mathlib) build-verification worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/440-MAINT-section3-build-f` (git branch `erenup/440-MAINT-section3-build-f`, based on
`origin/erenup/integration-section3` after the merges #339–#353 (T13 `Assembly` + contract `T02.localization` (46 contracts), T12 `HaarCube`/`CutoffGagliardo`, T15 `Placement`? (not yet)/`Scaling`,
T17 `Transport`/`LatticeDeriv`/`CorrectionDeriv`/`ForceDeriv`/`ForceProfile`, T20 `CriticalRegularity`, T22 `Domain`/`RestrictBridge`/`WeightRatio`/`OrderZeroIsometry`). Read `CLAUDE.md` and the previous report
**`logs/SECTION3_BUILD_20260918d.md`** (reproduce its structure and tables exactly; it is the template).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6` (the toolchain is already installed here).
- **Do not fix anything.** This is a read-only check of the Lean tree: if a module fails, record the exact error text and the module,
  do not edit `.lean` files. The only tracked edits allowed are the report file and the ledger fix in deliverable 2.
- Report facts only: exit codes, counts, wall time, exact error/warning lines. No summaries that are not backed by a command output.

## Deliverable 1 — `logs/SECTION3_BUILD_20260918f.md` (same sections as the template)
1. Environment table (commit checked = `git rev-parse HEAD`, toolchain, threads).
2. Module inventory: `find formalization/NSFormalization/Section3 -name '*.lean' | sort` (expect about 75: T10 7, T11 30, T12 7, T13 7, T14 1, T15 4, T16 4, T17 6, T20 1, T22 4 — count them,
   do not trust this expectation) and per-directory counts.
3. **Full rebuild of every Section 3 module in one `lake build` command**: first delete only the Section 3 build products
   (`formalization/.lake/build/lib/lean/NSFormalization/Section3/` and `…/ir/NSFormalization/Section3/`), then
   `cd verification && time LEAN_NUM_THREADS=6 lake build <all Section 3 module names>` with output to `tmp/section3_build.log`
   (`tmp/` is gitignored). Record exit code, wall time, `grep -c 'error'`, Built/Replayed counts for Section 3 modules, warning lines and
   `grep -c 'warning: NSFormalization/Section3/'` (expect 0 — verify), `.olean` count on disk, `grep -rn sorry formalization/NSFormalization/Section3`.
4. Gates from the worktree root: `make check`, `make test` (expect all 46 contracts `checked; standard logical axioms only` — record the
   actual count), `make test-mutations`, `python3 experiments/check_contracts.py --base-ref main` (record `registered_contracts` (expect 42) and
   `base_compatibility_checked`).
5. Probe + axioms scan: every `research/T1*/**/*_closes.lean`, `research/T1*/axioms_*.lean`, `research/T1*/probes/api_on_canonical.lean`,
   and `research/T11/probes/assembly_closes.lean`, each with `cd verification && lake env lean ../<file>` (4-way parallel, `LEAN_NUM_THREADS=2`
   each); table of pass/fail with the number of files; every failing file with its first error line. Axioms lines must all be
   `[propext, Classical.choice, Quot.sound]` — grep for any other axiom name and report the count (expect 0).
6. Conclusion section: one paragraph, facts only; a list of anything that is not green.

## Report
Commit on your branch (one commit: the build report). End with four parts (what was checked / what is in the tree now (counts) /
what is not green (exact text) / commands run and results). Also write it to `research/MAINT/REPORT_440.md`.
