# Lane 243-SPEC-r46-draft-b — double-blind specification of Proposition 4.6 "prop:Renergy" (R46: density in the completed force spaces and strong trajectory closure): draft B

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/243-SPEC-r46-draft-b` (git branch `erenup/243-SPEC-r46-draft-b`, based on `origin/erenup/integration`). This is one of two
**independent, mutually invisible** drafts (rule 2 of `CLAUDE.md`): write the Lean statement from the manuscript and the registered vocabulary only. **Do NOT read**
`research/section4/STATEMENTS.md`, `research/R46*`, `research/R41*`, `collaboration/briefs/`, or any file whose name mentions R46/Renergy/RMain.

Read: `CLAUDE.md` (contract import rules; no placeholder `Prop`s; docstrings cite paper lines), `formalization/blueprint/tasks.json` entry for **R46** only, the paper:
`04-whole-space.tex:218-296` (prop:Renergy statement and proof — the proof only to learn what the statement quantifies over: the completed spaces `L^q(0,∞;H^s)` and `L²(0,∞;Ḣ^{-1})`,
the datum-path realizations, the strong trajectory closure in the energy space), `02-preliminaries.tex:55-80` (the completions, `Ḣ^{-1}`, the energy space `E_T`), and the registered
vocabulary: `verification/Contracts/V1/Data.lean` (`forceSobolevENorm`, `forceHomogeneousENorm` `:225-236,:390-410`; the classes `:509-580`; `breakdownSetIn`, `RelativelyDense` `:660-712`;
the **completed-space density predicate** documented right after `BreakdownDenseR` (`:713-760`: "density of `S` in the full Bochner space over the completion, parametric in the realization
`path`" — read its exact definition and the two instantiations it describes), `verification/Contracts/V1/BochnerPartial.lean`, `HomogeneousPartial.lean`, `Scaling.lean` (whatever they
register about datum paths / Bochner norms / `Ḣ^{-1}`), `verification/Contracts/V1/InsertionFamily.lean:300-330` (`energyRate`, `forceConvergence` — the Theorem 4.2 clauses the
proposition's second part re-uses), and one registered contract as a formatting template (`verification/Contracts/V1/CriticalRegularity.lean`).

## Deliverables (statements only, no proofs)
1. `research/R46/DraftB.lean` (create the directory): a Lean file that **elaborates** (`cd verification && lake env lean ../research/R46/DraftB.lean`) containing `structure REnergyAPI`
   (or your name) with one field per clause of Proposition 4.6 exactly as stated — the density assertions in each completed space (with the realization the paper uses for each), and the
   strong trajectory-closure assertion(s) — docstrings citing `04-whole-space.tex:<line>`, exact quantifier order; local verbatim definitions (flagged "needs registration") for notions absent
   from the registered vocabulary.
2. `research/R46/COMPARISON_B.md`: paper-clause → Lean field table; choices (how the completion/Bochner space is represented; which realization `path` each clause uses; how "strong closure
   of trajectories" is rendered); ambiguities.
3. Commit on your branch (never push/merge/rebase). Report in four parts and write it to `research/R46/REPORT_243.md`.
