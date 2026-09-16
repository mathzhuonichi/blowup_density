# Lane 277-SPEC-t10-spec — produce the reconciled specification of T10 (periodic data layer) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/277-SPEC-t10-spec` (git branch `erenup/277-SPEC-t10-spec`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/T10/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/263-SPEC-t10-draft-a:research/T10/DraftA.lean`, `git show erenup/263-SPEC-t10-draft-a:research/T10/COMPARISON_A.md`,
`git show erenup/264-SPEC-t10-draft-b:research/T10/DraftB.lean`, `git show erenup/264-SPEC-t10-draft-b:research/T10/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/T10/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_263.md`, `REPORT_264.md` copied verbatim from the two branches (provenance).
2. `research/T10/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing `04-whole-space.tex:<line>` and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/T10/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/T10/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/T10/REPORT_277.md`; commit on your branch.

## T10-specific
The reconciliation asks you to (a) base the spec on draft B, (b) add the homogeneous datum/norm, (c) mirror `Data.lean:624-656` `ClassicalSolutionR` field names/order in `ClassicalSolutionT`, (d) **quote the paper lines defining `𝒳_𝕋` and `𝓕_𝕋`** (`grep -n "mathcal X\|mathcal F\|\\TT" paper/sections/03-torus.tex paper/sections/02-preliminaries.tex`) and settle the class definitions by the paper, recording both drafts' readings in COMPARISON.md; (e) list in COMPARISON.md §"Needs a lemma" the union of both drafts' lists (these become T10's proof lanes).
