# Lane 275-SPEC-t22-draft-a — Section 3 node T22 "bounded-domain norm layer (restriction / zero extension)": double-blind draft A of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/275-SPEC-t22-draft-a` (git branch `erenup/275-SPEC-t22-draft-a`, based on `origin/erenup/integration-section3`). One of two **independent, mutually invisible** drafts
(rule 2 of `CLAUDE.md`): **do NOT read** `research/T22/`, `research/T10/`, `research/T12/`, `research/T13/`, `research/T16/`, or `collaboration/briefs/` entries for other T22/T10 lanes.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1 (representation: periodic fields on ℝ³ as the physical layer;
coefficient side `lp (Fin 3 → ℤ) 2` with weight `(1+4π²|k|²)^{s/2}`) and the **T22 row** of §3 (`grep -n "T22" collaboration/SECTION3_PLAN.md`), the task card `collaboration/tasks/T22.md`
(contract sentence, dependencies, evidence), the paper: `03-torus.tex` the bounded-domain layer displays `eq:restriction-norm` and `eq:zero-extension` (grep the labels; read the surrounding paragraph): restriction of an `H^s(ℝ³)` field to the cube / zero extension of a compactly supported field, with multiplier bounds whose constants are independent of `ε`, `02-preliminaries.tex:1-80`, the registered ℝ³ vocabulary `verification/Contracts/V1/Data.lean` (`:150-260`, `:375-410`,
`:509-580`) and the Section 4 contracts named below as **templates**, and Mathlib names you use (`#check`).
Section 4 counterpart: D01`s datum architecture (`Data.lean:150-260`) and B02`s cutoff/annular lemmas (`Contracts/V1|V2/HomogeneousPartial.lean` `annularRestriction`, `annularSmoothing`) — reuse the ℝ³ side verbatim; only the torus side is new.

## Deliverables (statements only, no proofs)
1. `research/T22/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T22/DraftA.lean`) with a `structure <Name>API : Prop` (or a
   data-carrying structure where the paper's object is an existential family) whose fields are exactly the clauses of the node's target statement(s); constants explicit; local verbatim
   definitions flagged "needs registration / to be aligned with T10". Docstrings cite `<file>.tex:<line>`; exact quantifier order.
2. `research/T22/COMPARISON_A.md`: paper-clause → Lean field table; choices; ambiguities; "needs a lemma" list; which Section 4 results are the counterparts and what can be reused verbatim.
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T22/REPORT_275.md`.
