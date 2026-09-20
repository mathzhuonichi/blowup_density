# Lane 290-SPEC-t12-spec — produce the reconciled specification of T12 (mean-zero periodic Sobolev calculus and critical embeddings (`lem:calculus` + `lem:critical-embeddings`, torus halves)) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/290-SPEC-t12-spec` (git branch `erenup/290-SPEC-t12-spec`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/T12/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/269-SPEC-t12-draft-a:research/T12/DraftA.lean`, `git show erenup/269-SPEC-t12-draft-a:research/T12/COMPARISON_A.md`,
`git show erenup/270-SPEC-t12-draft-b:research/T12/DraftB.lean`, `git show erenup/270-SPEC-t12-draft-b:research/T12/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/T12/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_269.md`, `REPORT_270.md` copied verbatim from the two branches (provenance).
2. `research/T12/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing the cited paper file and line (`appendix-a-local-theory.tex:<line>`, `appendix-b-embeddings.tex:<line>`, `03-torus.tex:<line>`, `02-preliminaries.tex:<line>`) and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/T12/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/T12/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/T12/REPORT_290.md`; commit on your branch.

## T12-specific instructions (binding)
- **Vocabulary**: copy the T10 declarations you use verbatim from `research/T10/Spec.lean` **as amended** (lead amendment 1, `research/T10/RECONCILIATION.md` §5:
  `IsPeriodicDatum`/`IsPeriodicHomogeneousDatum` carry `Integrable (torusLift z) periodicTorusMeasure`), following the T13 copy policy (`research/T13/Spec.lean:18-21`,
  marker comments with the source line). The scalar mirror pair (`IsPeriodicScalarDatum`, `periodicScalarSobolevENorm`) must be spelled exactly like T10's vector pair, including the
  integrability conjunct.
- **API shape**: one **Type-valued** `structure MeanZeroSobolevCalculusAPI where` with the constants as data fields first (`Cproduct : ℕ → ℝ`, `Cproduct_pos`, `Cinfty`, …, `Cgap : ℝ → ℝ`,
  `Cgap_pos : ∀ s, 0 ≤ s → 0 < Cgap s`), then the nine clauses in the reconciliation's §3 table order (incl. the two added fields `lambda_exists`, `homogeneous_le_sobolev`). Mirror
  `verification/Contracts/V1/GradientL6.lean` token-for-token for `lift`/`gradientTensor`/`laplacian` and the field spelling of `gradientLSix`; import that contract file to check
  with `example … := rfl` where the reconciliation says the spelling is identical.
- **Non-vacuity**: every field's docstring states why it is not vacuous (which hypothesis supplies a witness); for `gradientLambdaCriticalL3` cite `lambda_exists`.
- Report the elaboration of `research/T12/Spec.lean` and the `rfl` checks; do not prove anything.
