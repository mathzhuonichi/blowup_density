# Lane 270-SPEC-t12-draft-b — Section 3 node T12 "mean-zero Sobolev calculus and critical embeddings": double-blind draft B of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/270-SPEC-t12-draft-b` (git branch `erenup/270-SPEC-t12-draft-b`, based on `origin/erenup/integration-section3`). One of two **independent, mutually invisible** drafts
(rule 2 of `CLAUDE.md`): **do NOT read** `research/T12/`, `research/T10/`, `research/T13/`, or `collaboration/briefs/` entries for other T12/T10 lanes.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1 (representation: periodic fields on ℝ³ as the physical layer;
coefficient side `lp (Fin 3 → ℤ) 2` with weight `(1+4π²|k|²)^{s/2}`; homogeneous `|2πk|^s`; mean-zero subspace = `k = 0` coefficient zero) and the **T12 row** of §3 (`grep -n "T12" collaboration/SECTION3_PLAN.md`),
the task card `collaboration/tasks/T12.md` (contract sentence, dependencies, evidence), the paper: the mean-zero Sobolev calculus and critical embeddings on T³: `eq:Rproduct` (the tame product/algebra estimate), `‖v‖_∞ ≤ C‖v‖_{H²}`, `‖v‖₃ ≤ C‖v‖_{Ḣ^{1/2}}`, `‖∇v‖_{L⁶}` — find them by `grep -n "Rproduct\|critical-embeddings\|mean-zero\|mean zero" paper/sections/*.tex` and read the lemma statements and the surrounding definitions; the Section 4 counterparts are A03 (`Contracts/V1/TameProduct.lean`, `BoundedRepresentative.lean`) and A05 (`Contracts/V1/GradientL6.lean`, `Contracts/V2/GradientL6.lean` `velocityCriticalL3`) — copy their statement shapes with mean-zero periodic fields, `02-preliminaries.tex:1-80` (shared definitions), the registered ℝ³ vocabulary
`verification/Contracts/V1/Data.lean` (`:150-260`, `:375-410`, `:509-580`) as the **template** for spelling (copy its style with T³ objects), the local periodic layer heads
(`formalization/NSFormalization/Paper1/PeriodicSobolev*.lean`, `PeriodicMeanZero*.lean`, `TorusCube.lean` — `grep -nE "^(def|structure|theorem) "` only), and Mathlib names you use (`#check`).
Uniformity note: on the torus the critical embedding `H^{1/2} ↪ L³` holds only for mean-zero fields (or with the `L²` term added); state exactly what the paper states.

## Deliverables (statements only, no proofs)
1. `research/T12/DraftB.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T12/DraftB.lean`) with a `structure <Name>API : Prop` whose fields are
   exactly the clauses of the node's target statement(s) (one field per inequality/identity, constants as explicit `ℝ` fields with positivity where the paper says "universal constant"),
   plus the local verbatim definitions it needs (periodic Sobolev/homogeneous datum and norm, mean-zero part, …) flagged "needs registration / to be aligned with T10". Docstrings cite
   `<file>.tex:<line>`; exact quantifier order.
2. `research/T12/COMPARISON_B.md`: paper-clause → Lean field table; choices; ambiguities; "needs a lemma" list; which ℝ³ (Section 4) results are the counterparts (name the Section 4 module/contract).
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T12/REPORT_270.md`.
