# Lane 248-SPEC-r41-spec — produce the reconciled specification of R41 (thm:Rmain) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/248-SPEC-r41-spec` (git branch `erenup/248-SPEC-r41-spec`, based on `origin/erenup/integration`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/R41/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/236-SPEC-r41-draft-a:research/R41/DraftA.lean`, `git show erenup/236-SPEC-r41-draft-a:research/R41/COMPARISON_A.md`,
`git show erenup/237-SPEC-r41-draft-b:research/R41/DraftB.lean`, `git show erenup/237-SPEC-r41-draft-b:research/R41/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/R41/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_236.md`, `REPORT_237.md` copied verbatim from the two branches (provenance).
2. `research/R41/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing `04-whole-space.tex:<line>` and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/R41/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/R41/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/R41/REPORT_248.md`; commit on your branch.

## R41-specific
The reconciliation also compares against the earlier skeleton `research/section4/STATEMENTS.md` §1(iv) (you MAY read it now) and lists in §4 the landed theorems that will bind each field (lanes 232/233/235); in `COMPARISON.md` add a §"Binding plan" mapping each field to those theorems with the exact adaptation needed (the `q : ℝ≥0∞` convention vs 232 real `q`; the `↔` from 232 + 235).
