# Lane 241-SPEC-r47-draft-b — double-blind specification of Theorem 4.7 "thm:Rgrid" (R47: identical whole-space cell observations): draft B

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/241-SPEC-r47-draft-b` (git branch `erenup/241-SPEC-r47-draft-b`, based on `origin/erenup/integration`). This is one of two
**independent, mutually invisible** drafts (rule 2 of `CLAUDE.md`): write the Lean statement from the manuscript and the registered vocabulary only. **Do NOT read**
`research/section4/STATEMENTS.md`, `research/R47*`, `research/R42/COMPARISON.md` §6, `collaboration/briefs/`, or any file whose name mentions R47/Rgrid.

Read: `CLAUDE.md` (contract import rules; no placeholder `Prop`s; docstrings cite paper lines), `formalization/blueprint/tasks.json` entry for **R47** only, the paper:
`04-whole-space.tex:297-330` (thm:Rgrid statement and proof — read the proof only to learn which objects the statement quantifies over: the cell/grid, the observation functionals, the
inserted family from Theorem 4.2 `:31-60`), `02-preliminaries.tex` (definitions of the observation/cell notions if they live there — grep `grid`, `cell`, `observ`), and the registered
vocabulary `verification/Contracts/V1/Data.lean` (classes, `ClassicalSolutionR`, `maximalLifespanR`, `RegularThrough`), `verification/Contracts/V1/InsertionFamily.lean:125-330`
(the registered Theorem 4.2 record `InsertionFamilyAPI` — its support/difference fields `velocityDifference_support`, `velocityDifference_divFree`, `pressureDifference_support`,
`forceDifference_ball`, `history` are the objects a "cell observation" statement will refer to; you may quantify over an `InsertionFamilyAPI` record or over the raw data — say why),
and one registered contract as a formatting template (`verification/Contracts/V1/CriticalRegularity.lean`).

## Deliverables (statements only, no proofs)
1. `research/R47/DraftB.lean` (create the directory): a Lean file that **elaborates** (`cd verification && lake env lean ../research/R47/DraftB.lean`) containing `structure RGridAPI`
   (or your name) with one field per clause of Theorem 4.7 exactly as stated, docstrings citing `04-whole-space.tex:<line>`, exact quantifier order; local verbatim definitions (flagged
   "needs registration") for any notion absent from the registered vocabulary (cells, observation maps, "identical observations").
2. `research/R47/COMPARISON_B.md`: paper-clause → Lean field table; choices; ambiguities (what "identical" means precisely — equality of the observed fields on the cell for all times
   before/at which time?; which family the theorem refers to).
3. Commit on your branch (never push/merge/rebase). Report in four parts and write it to `research/R47/REPORT_241.md`.
