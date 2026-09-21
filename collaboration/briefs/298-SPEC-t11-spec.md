# Lane 298-SPEC-t11-spec — produce the reconciled specification of T11 (periodic local theory and continuation (`prop:local` on T³ + Appendix A mean reduction and viscosity rescaling)) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/298-SPEC-t11-spec` (git branch `erenup/298-SPEC-t11-spec`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/T11/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/288-SPEC-t11-draft-a:research/T11/DraftA.lean`, `git show erenup/288-SPEC-t11-draft-a:research/T11/COMPARISON_A.md`,
`git show erenup/289-SPEC-t11-draft-b:research/T11/DraftB.lean`, `git show erenup/289-SPEC-t11-draft-b:research/T11/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/T11/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_288.md`, `REPORT_289.md` copied verbatim from the two branches (provenance).
2. `research/T11/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing the cited paper file and line (`02-preliminaries.tex:<line>`, `appendix-a-local-theory.tex:<line>`, `03-torus.tex:<line>`) and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/T11/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/T11/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/T11/REPORT_298.md`; commit on your branch.

## T11-specific instructions (binding)
- **Vocabulary**: copy the T10 declarations you use verbatim from `research/T10/Spec.lean` **as amended** (lead amendment 1, `research/T10/RECONCILIATION.md` §5), T13 copy policy
  (`research/T13/Spec.lean:18-21`, marker comments with source lines); the data layer up to `IsPeriodicReweight` is registered as `T01.torus_data` (`verification/Contracts/V1/TorusData.lean`)
  — you may import that contract and check your copies against it with `example … := rfl`; the solution-class declarations (`IsPeriodicSobolevPath`, force norms/classes, pressure gauge,
  `ClassicalSolutionT`, lifespan, breakdown) are not registered yet — copy them verbatim.
- **Structures and fields exactly as `research/T11/RECONCILIATION.md` §3 lists them** (four API structures: `PeriodicLocalRegularity` (3 fields, `Prop`), `PeriodicLocalTheoryAPI : Type` (8),
  `PeriodicContinuationAPI : Prop` (5), `PeriodicMeanReductionAPI : Prop` (6), `PeriodicViscosityRescalingAPI : Prop` (4)), with the T11-local defs named there (`IsPeriodicSobolevPathOn`,
  `convectionDivergenceT`, `scalarSpatialLaplacianT`, `SolvesBelowT`, `IsMaximalPeriodicSolution`, `ExtendsBeyondT`, `timeShiftT`, the data-defined Galilean mean `galileanMeanT a f t := meanT a + ∫₀ᵗ meanT (f s)`
  and the transforms built from it). Mirror the registered Section 4 spellings the reconciliation cites (`Contracts/V2/Continuation.lean`: `SolvesBelow`, `IsMaximalSolution`, `squaredHTwoIntegral`;
  `Contracts/V2/LocalTheory.lean`: `convectionDivergence`) token-for-token and check with `example … := rfl` where both sides elaborate in the same file.
- **No junk-value traps**: every norm/integral statement carries the integrability or class hypotheses the reconciliation specifies; the Galilean force uses the data-defined mean (no `fderiv` of a
  possibly non-differentiable function; if a derivative is needed, state `HasDerivAt` as a field hypothesis/conclusion exactly as the reconciliation says).
- Report the elaboration of `research/T11/Spec.lean` and the `rfl` checks; do not prove anything.
