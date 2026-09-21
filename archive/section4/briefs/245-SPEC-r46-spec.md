# Lane 245-SPEC-r46-spec — produce the reconciled specification of R46 (prop:Renergy) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/245-SPEC-r46-spec` (git branch `erenup/245-SPEC-r46-spec`, based on `origin/erenup/integration`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/R46/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/242-SPEC-r46-draft-a:research/R46/DraftA.lean`, `git show erenup/242-SPEC-r46-draft-a:research/R46/COMPARISON_A.md`,
`git show erenup/243-SPEC-r46-draft-b:research/R46/DraftB.lean`, `git show erenup/243-SPEC-r46-draft-b:research/R46/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/R46/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_242.md`, `REPORT_243.md` copied verbatim from the two branches (provenance).
2. `research/R46/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing `04-whole-space.tex:<line>` and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/R46/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/R46/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/R46/REPORT_245.md`; commit on your branch.
