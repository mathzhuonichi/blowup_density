# Lane 502-MAINT-core-refresh — refresh the generated artifacts on `erenup/core` after merging closing lanes

Worktree `/data_8T/ping/blowup_density/.claude/worktrees/502-MAINT-core-refresh` (branch `erenup/502-MAINT-core-refresh`, = `origin/erenup/core` after the lead merged several Phase 5 closing lanes; each lane regenerated `formalization/blueprint/{DEPENDENCY_GRAPH.md,AXIOM_AUDIT.json}`, the README/CLOSURE_AUDIT counts and `output/pdf/*.pdf` on its own branch, so the merged tree is stale/inconsistent). Read `collaboration/briefs/COMMON_PHASE5.md` §3, `experiments/README.md`, `experiments/check_formalization_plan.py` (regeneration + `--check`), `experiments/audit_article_axioms.py` (header: where it writes and how `AXIOM_AUDIT.json` / the "Source changed: rerun the article axiom audit" check work), `experiments/check_reader_documents.py` (what `make paper` verifies).

## Ground rules
Work ONLY inside this worktree; never push/merge/rebase; commit on your branch. `. scripts/lean-env.sh`; `lake` only from `verification/`, `LEAN_NUM_THREADS=6`. **No Lean edits.** Only generated/derived files: `DEPENDENCY_GRAPH.md`, `AXIOM_AUDIT.json`, `RESULT_MAP.md` (consistency only), `CLOSURE_AUDIT.md` and `README.md` counts/lists of remaining Partial entries, `paper/formalization_guide.tex` (only if a coverage row is inconsistent with `proof_graph.json`), `output/pdf/*.pdf` via `make paper`.

## Goal
1. `python3 experiments/check_formalization_plan.py` (regenerate), then `--check`.
2. `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2`; update `AXIOM_AUDIT.json` as the script prescribes; confirm every audited declaration has only `propext, Classical.choice, Quot.sound`.
3. Make the counts consistent everywhere: `proof_graph.json` is the source of truth; README ("N Closed and M Partial", the list of remaining Partial entries), `CLOSURE_AUDIT.md` (same list + its "The other Partial entries are …" sentence), `DEPENDENCY_GRAPH.md` (generated), the guide's `\coverage{…}` rows, `RESULT_MAP.md` Coverage column.
4. `make check`, `make test`, `make test-mutations`, `make paper` — all must be green; quote the summaries.
Report `research/MAINT/REPORT_502.md` (four parts). Commit.
