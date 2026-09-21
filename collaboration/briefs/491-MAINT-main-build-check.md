# Lane 491-MAINT-main-build-check — full compile check of the owner's new `main` (as `erenup/core`) after the 2026-09-21 streamlining commit

You are a Lean 4 (v4.34.0-rc2 + Mathlib) build-verification worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/491-MAINT-main-build-check` (git branch `erenup/491-MAINT-main-build-check`, = `origin/erenup/core` = `origin/main` @ `1a1b53b6` + the lead's process layer). The owner's commit changed `formalization/lakefile.toml` (HeliCorgi roots trimmed, `FormalPatched` removed, local library `globs = ["NSFormalization.+"]`),
pruned `vendor/` and `formalization/` to the modules used by the 29 registered contracts, and added new checks. Read `README.md` (owner), `experiments/README.md`, `verification/README.md`, `formalization/blueprint/README.md`, and the previous report template `logs/SECTION3_BUILD_20260919i.md` (reproduce its structure).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. **Do not fix anything**: if a module fails, record the exact error text; do not edit `.lean` files or `lakefile.toml`. The only tracked edit is the report.
- Facts only: exit codes, counts, wall time, exact error/warning lines.

## Deliverable — `logs/MAIN_BUILD_20260920.md`
1. Environment table (commit checked = `git rev-parse HEAD` and `git rev-parse origin/main`, toolchain, Mathlib rev from `verification/lake-manifest.json`, threads).
2. Module inventory: `find formalization/NSFormalization -name '*.lean' | wc -l` per top directory (Section3/T*, Section4/*, Source, Paper1, Paper3, …), plus the HeliCorgi roots listed in `formalization/lakefile.toml`.
3. **Full rebuild in one `lake build`**: delete `formalization/.lake/build/lib/lean/NSFormalization/` and `…/ir/NSFormalization/` (only those), then `cd verification && time LEAN_NUM_THREADS=6 lake build <every NSFormalization module name from the find>` → `tmp/main_build.log`; record exit code, wall time, `grep -c 'error'`, Built/Replayed counts, all warning lines from `NSFormalization/` (expect the T22 one gone), `.olean` count. Then `lake build` of every `Bindings.*` and `Tests.*` module (list from `verification/`), same records.
4. Gates from the worktree root: `make check`, `make test` (record the number of `standard logical axioms only` lines; expect 29), `make test-mutations`, `python3 experiments/check_contracts.py --summary`, `python3 experiments/check_formalization_plan.py --check`, and `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2` (record its summary: number of declarations audited, any non-standard axiom; compare with `formalization/blueprint/AXIOM_AUDIT.json`).
5. `make paper` (LaTeX is installed: latexmk/pdflatex): record exit code and the `check_reader_documents.py` summary; if it fails, the exact first error.
6. Conclusion: one paragraph, facts only; a list of anything not green.

## Report
Commit on your branch (one commit: the report). End with four parts (what was checked / what is in the tree (counts) / what is not green (exact text) / commands and results). Also write it to `research/MAINT/REPORT_491.md`.
