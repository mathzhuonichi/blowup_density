# Lane 268-MAINT-ledger-t10-t24 — add the Section 3 nodes T10–T24 to the blueprint DAG and the work-item ledger (engineering/ledger only; no Lean)

You are a repository-maintenance worker on the checkout at your working directory `/data_8T/ping/blowup_density/.claude/worktrees/268-MAINT-ledger-t10-t24` (git branch
`erenup/268-MAINT-ledger-t10-t24`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md`, `collaboration/SECTION3_PLAN.md` (§3 the T10–T24 table: goal, dependencies, size, model,
bucket mapping T01–T04; §6 ledger/numbering rules), `archive/section4/REPORT_267.md` §3 (the exact fields the DAG and ledger need: DAG `id/title/priority/contract/dependencies/evidence`,
ledger `id/kind/state/owner/contracts/deliverable`), `formalization/blueprint/tasks.json` (the DAG; the existing `T01`–`T04` bucket entries and a Section 4 node such as `D01`/`R43` as
templates), `formalization/blueprint/DEPENDENCY_GRAPH.md` (the Mermaid graph — add the T10–T24 nodes and edges), `collaboration/work_items.json` (ledger; `T01`–`T04` and `D01` as templates),
`experiments/tasks.py` (`--help`, `render`), `experiments/check_work_queue.py` (what `make check` validates — ids must match between DAG and ledger; task cards regenerated), and
`research/T10/`, `research/T13/` (RECONCILIATION/COMPARISON files exist for T13; T10's drafts are on branches 263/264 — use their paths as `evidence`).

## Goal
1. `formalization/blueprint/tasks.json`: one entry per node T10–T24 with `id`, `title` (from SECTION3_PLAN §3, Chinese ok but keep the paper labels e.g. `lem:localization`), `priority` (P1 for the
   critical path T10→T11→T18→T19→T21 and T13/T20; P2 otherwise), `contract` (one sentence: the exact statement target, e.g. T13 = `lem:localization` as reconciled in `research/T13/RECONCILIATION.md`),
   `dependencies` (from the table; T10 depends on nothing; keep the bucket parents T01–T04 as in §3's last column via whatever field the existing entries use for buckets), `evidence`
   (paths: paper section lines, `research/T1x/` files, the vendor/local modules named in §2/§3). Keep the JSON style of the file (`ensure_ascii=False`, 2-space indent).
2. `formalization/blueprint/DEPENDENCY_GRAPH.md`: add the nodes and edges (T10 → T11/T12/T13/T14/T16/T22; T13 → T15/T17; T11 → T18; T20 → T21; T18 → T19 → T21; T23 after T18/T22; T24 …
   — follow §3 exactly).
3. `collaboration/work_items.json`: one ledger entry per node (`kind`: specification for all until a contract is registered; `state`: `needs-specification` for T10/T13 (drafts exist),
   `open` for the rest — or whatever the checker's allowed states are; `owner`: unassigned; `contracts`: []; `deliverable`: the reconciled `research/T1x/Spec.lean` + registration).
4. `python3 experiments/tasks.py render`; `make check` must pass (paste the last lines). Do not edit generated files by hand.

## Ground rules
Work ONLY inside this worktree; never push/merge/rebase; commit on your branch. No Lean, no `verification/`, no `research/` edits. If the checker rejects a field/state, adapt to what it
accepts and report the mapping.

## Report
Four parts; write it to `collaboration/REPORT_268.md` (this file may be moved by the lead later).
