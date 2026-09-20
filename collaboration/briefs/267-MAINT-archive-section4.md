# Lane 267-MAINT-archive-section4 — archive the Section 4 working documents and refocus the repository's live documents on Section 3 (no Lean changes)

You are a repository-maintenance worker (docs/ledgers only; **no Lean edits, no changes under `verification/`, `formalization/`, `research/`, `paper/`, `logs/AGENT_RUNS.csv`, `logs/LESSONS.md`**) on the
checkout at your working directory `/data_8T/ping/blowup_density/.claude/worktrees/267-MAINT-archive-section4` (git branch `erenup/267-MAINT-archive-section4`, based on
`origin/erenup/integration-section3` — the new Section 3 core branch; `erenup/integration` is the frozen Section 4 deliverable, do not touch it). Read `CLAUDE.md` (esp. the new "分节分支" bullet),
`collaboration/SECTION3_PLAN.md` (the Section 3 plan: nodes T10–T24, stages S3-0…S3-3, ledger rules §6), `PLAN.md` (structure: §1–§7 Section 4 overview, §8 the lane table with ~260 rows),
`NEXT_SESSION.md` (long timeline), `collaboration/HANDOFF.md` (Section 4 packages P1–P11 + a Section 3 note), `collaboration/briefs/` (one brief per lane, 011–266), `collaboration/work_items.json`
+ `experiments/tasks.py` (`--help`; `render` regenerates `collaboration/tasks/*.md` and `TASKS.md` — generated files, never hand-edit), and `logs/LESSONS.md` top 40 lines.

## Goal
Section 4 is complete (37 registered contracts, PR #259 to `main`). Make the **live** documents Section-3-first while keeping every Section 4 record reachable and unchanged in content:
1. Create `archive/section4/` with `README.md` (what is here, where the live Section 4 deliverable lives: branch `erenup/integration`, PR #259, contracts 1–37, `research/<ID>/`), and move there via
   `git mv` (history preserved): `PLAN.md` → `archive/section4/PLAN_SECTION4.md` (the whole file), `NEXT_SESSION.md` → `archive/section4/NEXT_SESSION_SECTION4.md`, `collaboration/HANDOFF.md` →
   `archive/section4/HANDOFF_SECTION4.md`, and `collaboration/briefs/<NNN>-*.md` for every lane **≤ 262** → `archive/section4/briefs/` (keep 263+ in place: they are Section 3).
2. Write the new live documents (Chinese, concise, same conventions):
   - `PLAN.md`: Section 3 plan front page: a 10-line status header (Section 4 done → archive link; Section 3 branch; stage now = S3-0), §1 the DAG summary (copy the T10–T24 table from
     `SECTION3_PLAN.md` §3 or link to it — do not duplicate the long text), §2 staging S3-0…S3-3 (link), §8 the **lane table** with the same columns as the archived one, containing only the
     Section 3 rows (263, 264, 265, 266, 267 — copy their rows verbatim from the archived table; the lead's `tmp/plan_row.py` appends/sets rows by lane name and expects the same table
     format: check the archived file's table header and keep it byte-identical; keep the rule "lane numbers are global and unique, next = 268").
   - `NEXT_SESSION.md`: Section 3 current state only (from the archived file's last ~6 entries: T10 draft A done, draft B lane 264 running, T13 drafts done + `research/T13/RECONCILIATION.md`,
     next = T10 reconciliation → T10 spec lane → T13 spec lane → register `T01.torus_data`; the branch switch; the owner-pending items of Section 4 as one line with the archive link).
   - `collaboration/HANDOFF.md`: Section 3 packages (one row per stage-S3-1 leaf T13/T16/T12/T14/T22 and the S3-2 mainlines T11/T20, with "claimable after" conditions), the external
     lane-number range, and the archive link.
3. Task ledger: for every Section 4 node (D01…R47, A0x, Bxx, Cxx, Ixx, Uxx) whose contracts are all registered, set its state to the ledger's "done"/"complete" value **using
   `experiments/tasks.py`'s own commands** (read `--help`; if there is no such command, leave states unchanged and say so — do not hand-edit `work_items.json` beyond what the tool does), then
   `python3 experiments/tasks.py render`. Add the Section 3 nodes T10–T24 to the ledger **only if** `tasks.py` supports adding items and `SECTION3_PLAN.md` §6 gives their fields; otherwise report
   what the lead must add.
4. Fix links: `CLAUDE.md` header pointers (PLAN/NEXT_SESSION/HANDOFF/archive), `collaboration/SECTION3_PLAN.md` header, `README.md` if it links to moved files (`grep -rn "HANDOFF.md\|NEXT_SESSION.md\|PLAN.md" --include=*.md . | grep -v archive`).
5. `make check` must still pass (it validates the ledger and task cards). Run it and paste the last lines.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; commit on your branch (one commit per step is fine).
- `git mv` for moves; no content edits to archived files except a one-line "archived on 2026-09-17; live copy: …" banner at the very top.
- Do not run `lake`; do not touch anything Lean.

## Report
End with four parts (what moved / what the new live docs contain / what was left unchanged and why / commands). Write it to `archive/section4/REPORT_267.md`.
