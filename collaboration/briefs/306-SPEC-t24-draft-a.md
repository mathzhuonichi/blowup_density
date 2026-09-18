# Lane 306-SPEC-t24-draft-a — Section 3 node T24 "further constructions" (`prop:affine`, `prop:multiple`, `prop:conservative`): double-blind draft A of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/306-SPEC-t24-draft-a` (git branch `erenup/306-SPEC-t24-draft-a`, based on `origin/erenup/integration-section3`). One of two **independent, mutually invisible** drafts (rule 2 of `CLAUDE.md`):
**do NOT read** `research/T24/` or `collaboration/briefs/` entries for other T24 lanes. T24 = three independent leaves of `sec:variants` (`03-torus.tex:667-740`) built on the imported packet
(T14) and the scaling proposition (T15).

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1–§3 (the T24 row), the paper `paper/sections/03-torus.tex:667-740`
in full (Proposition `prop:affine` `:668-696` "infinite-dimensional variations away from the endpoints", Proposition `prop:multiple` `:697-722` "finitely many prescribed singular regions",
Proposition `prop:conservative` `:723-740` "conservative forcing from rest") with their proofs; read the exact statements, hypotheses, quantifier order, which objects come from `thm:insertion`
/ `prop:scaling` / `thm:packet`, and what each proposition adds. Then the reconciled Section 3 vocabulary these statements must be written in: the registered `T01.torus_data`
(`verification/Contracts/V1/TorusData.lean` — import and use its names), `research/T10/Spec.lean` (solution-class part: `ClassicalSolutionT`, `maximalLifespanT`, `breakdownSetT`, `forceClassT`,
`initialClassT`, `energyENormT`, `forceSobolevENormT`), `research/T14/Spec.lean` (`PacketImportAPI`), `research/T15/Spec.lean` (**binding for anything rescaled**: `PlacementData`, the rescaled
fields, `ScalingAPI` and its fields), and, for `prop:conservative`, the registered Section 4 counterparts if any (grep `verification/contracts.json` for `conservative`, `affine`, `multiple`;
Section 4's `R45.force_classes` / `R47.grid_observations` may share shapes — read their field statements). Skim `formalization/NSFormalization/Paper1/ConservativeForce.lean`,
`PeriodicNonpositiveForce.lean` heads (`grep -nE "^(def|structure|theorem) "`) for implementation candidates to cite (not to import).

## Deliverables (statements only, no proofs)
1. `research/T24/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T24/DraftA.lean`). Import `Contracts.V1.TorusData`
   (+ other contract files you cite) and copy **verbatim** (T13 copy policy: same names, namespaces `BlowupDensity.T10.Draft` / `BlowupDensity.T14.Draft` / `BlowupDensity.T15.Spec`, marker comments
   with source lines) only the still-unregistered declarations you use. Then, in a namespace `BlowupDensity.T24.DraftA`, state three separate structures `AffineVariationAPI`,
   `MultipleRegionsAPI`, `ConservativeForcingAPI` (Type-valued with constants as data fields where the paper has constants; `Prop` otherwise — say which and why), whose fields are exactly
   the clauses of the three propositions (e.g. for `prop:affine`: the infinite-dimensional affine family of forces with the same breakdown behaviour, the exact "away from the endpoints"
   support condition; for `prop:multiple`: finitely many prescribed centres/regions with simultaneous singular behaviour and the exact separation hypothesis; for `prop:conservative`:
   `f = ∇φ`-type forcing from rest producing breakdown, with the exact class of `φ`). Every field: docstring citing `03-torus.tex:<line>`, exact quantifier order, "non-vacuity" comment,
   **no junk-value traps** (integrability/class hypotheses on every norm; `ν > 0`; forces in `forceClassT`).
2. `research/T24/COMPARISON_A.md`: paper-clause → Lean field table (with Section 4 counterpart fields where they exist); choices; ambiguities; "needs a lemma" list; implementation candidates.
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T24/REPORT_306.md`.
