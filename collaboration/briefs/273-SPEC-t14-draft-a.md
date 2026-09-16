# Lane 273-SPEC-t14-draft-a — Section 3 node T14 "packet import and packet energy": double-blind draft A of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/273-SPEC-t14-draft-a` (git branch `erenup/273-SPEC-t14-draft-a`, based on `origin/erenup/integration-section3`). One of two **independent, mutually invisible** drafts
(rule 2 of `CLAUDE.md`): **do NOT read** `research/T14/`, `research/T10/`, `research/T12/`, `research/T13/`, `research/T16/`, or `collaboration/briefs/` entries for other T14/T10 lanes.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1 (representation: periodic fields on ℝ³ as the physical layer;
coefficient side `lp (Fin 3 → ℤ) 2` with weight `(1+4π²|k|²)^{s/2}`) and the **T14 row** of §3 (`grep -n "T14" collaboration/SECTION3_PLAN.md`), the task card `collaboration/tasks/T14.md`
(contract sentence, dependencies, evidence), the paper: `03-torus.tex` `thm:packet` (the imported blow-up packet interface — grep `label{thm:packet}` and read the statement) and Lemma `lem:packetenergy` with the display `eq:packetenergy` (grep; energy `M`, dissipation `D`, the initial quiet interval where the packet vanishes, the smooth zero extension to negative times), `02-preliminaries.tex:1-80`, the registered ℝ³ vocabulary `verification/Contracts/V1/Data.lean` (`:150-260`, `:375-410`,
`:509-580`) and the Section 4 contracts named below as **templates**, and Mathlib names you use (`#check`).
Section 4 counterpart: I01 (`verification/Contracts/V1/Packet.lean` `PacketAPI`, `Bindings/Packet.lean` `packet ν`; `SECTION3_PLAN.md` §3 says T14 reuses the registered `I01.packet`) — state which `PacketAPI` fields are literally reusable on the torus (the packet is compactly supported in space, so its periodization is the torus packet) and which torus-specific clauses `lem:packetenergy` adds.

## Deliverables (statements only, no proofs)
1. `research/T14/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T14/DraftA.lean`) with a `structure <Name>API : Prop` (or a
   data-carrying structure where the paper's object is an existential family) whose fields are exactly the clauses of the node's target statement(s); constants explicit; local verbatim
   definitions flagged "needs registration / to be aligned with T10". Docstrings cite `<file>.tex:<line>`; exact quantifier order.
2. `research/T14/COMPARISON_A.md`: paper-clause → Lean field table; choices; ambiguities; "needs a lemma" list; which Section 4 results are the counterparts and what can be reused verbatim.
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T14/REPORT_273.md`.
