# Lane 272-SPEC-t16-draft-b — Section 3 node T16 "local divergence-free cutoff (lem:potential)": double-blind draft B of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/272-SPEC-t16-draft-b` (git branch `erenup/272-SPEC-t16-draft-b`, based on `origin/erenup/integration-section3`). One of two **independent, mutually invisible** drafts
(rule 2 of `CLAUDE.md`): **do NOT read** `research/T16/`, `research/T10/`, `research/T13/`, or `collaboration/briefs/` entries for other T16/T10 lanes.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1 (representation: periodic fields on ℝ³ as the physical layer;
coefficient side `lp (Fin 3 → ℤ) 2` with weight `(1+4π²|k|²)^{s/2}`; homogeneous `|2πk|^s`; mean-zero subspace = `k = 0` coefficient zero) and the **T16 row** of §3 (`grep -n "T16" collaboration/SECTION3_PLAN.md`),
the task card `collaboration/tasks/T16.md` (contract sentence, dependencies, evidence), the paper: `03-torus.tex` Lemma `lem:potential` (grep `label{lem:potential}`; read the lemma and its proof paragraph): the radial vector potential `∇×A = v`, the smooth Urysohn cutoffs, `w_ε = −∇×(η_ε θ_ε A)` smooth divergence-free periodic, and the display `eq:bgzero` (grep it), `02-preliminaries.tex:1-80` (shared definitions), the registered ℝ³ vocabulary
`verification/Contracts/V1/Data.lean` (`:150-260`, `:375-410`, `:509-580`) as the **template** for spelling (copy its style with T³ objects), the local periodic layer heads
(`formalization/NSFormalization/Paper1/PeriodicSobolev*.lean`, `PeriodicMeanZero*.lean`, `TorusCube.lean` — `grep -nE "^(def|structure|theorem) "` only), and Mathlib names you use (`#check`).
The Section 4 counterpart is I02 (`Contracts/V1|V2/Correction.lean`, `Bindings/Correction.lean`: the corrected background `b_ε = v + w_ε`); state the torus version with the same field names where the objects coincide.

## Deliverables (statements only, no proofs)
1. `research/T16/DraftB.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T16/DraftB.lean`) with a `structure <Name>API : Prop` whose fields are
   exactly the clauses of the node's target statement(s) (one field per inequality/identity, constants as explicit `ℝ` fields with positivity where the paper says "universal constant"),
   plus the local verbatim definitions it needs (periodic Sobolev/homogeneous datum and norm, mean-zero part, …) flagged "needs registration / to be aligned with T10". Docstrings cite
   `<file>.tex:<line>`; exact quantifier order.
2. `research/T16/COMPARISON_B.md`: paper-clause → Lean field table; choices; ambiguities; "needs a lemma" list; which ℝ³ (Section 4) results are the counterparts (name the Section 4 module/contract).
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T16/REPORT_272.md`.
