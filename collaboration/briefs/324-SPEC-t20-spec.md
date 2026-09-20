# Lane 324-SPEC-t20-spec — produce the reconciled specification of T20 (global regularity for small critical force (`prop:critical`, torus)) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/324-SPEC-t20-spec` (git branch `erenup/324-SPEC-t20-spec`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md` (contract import rules; no placeholder
`Prop`s; docstrings cite paper lines), then **the lead's decisions** `research/T20/RECONCILIATION.md` (binding), and the two blind drafts (not on your base; read them with
`git show erenup/303-SPEC-t20-draft-a:research/T20/DraftA.lean`, `git show erenup/303-SPEC-t20-draft-a:research/T20/COMPARISON_A.md`,
`git show erenup/304-SPEC-t20-draft-b:research/T20/DraftB.lean`, `git show erenup/304-SPEC-t20-draft-b:research/T20/COMPARISON_B.md`), the paper lines they cite, and the registered
vocabulary `verification/Contracts/V1/Data.lean` (`criticalOrder` `:259`, `breakdownSetIn`/`RelativelyDense` `:672-712`, `CompletedDenseVia`/`CompletedDense`/`CompletedDenseHomogeneous`
`:732-750`, `energyENorm` §5, `IsSobolevPath` `:174`, `IsHomogeneousPath` `:375`), `Contracts/V1/InsertionFamily.lean` (the R42 record), `Contracts/V2/InsertionLifespan.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (field names, parametric shapes, `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`, which conjuncts to keep/drop).
  Where the reconciliation says "check `rfl`" (registered abbreviations vs `CompletedDenseVia`), verify it with an `example … := rfl` in the spec file and report.

## Deliverables
1. `research/T20/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_303.md`, `REPORT_304.md` copied verbatim from the two branches (provenance).
2. `research/T20/Spec.lean`: the reconciled statement — one `structure` in a `Draft`-style namespace, every field with a docstring citing the cited paper file and line (`03-torus.tex:<line>`, `02-preliminaries.tex:<line>`, `appendix-b-embeddings.tex:<line>`) and the exact
   quantifier order; **elaborates** (`cd verification && lake env lean ../research/T20/Spec.lean`, 0 errors); plus the `rfl` checks above and a "non-vacuity" comment per field.
3. `research/T20/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the reconciliation's rulings; §"Proof dependencies" copied from the reconciliation;
   §"Open questions for the owner".
4. Report in four parts; write it to `research/T20/REPORT_324.md`; commit on your branch.

## T20-specific instructions (binding)
- **Vocabulary**: `import Contracts.V1.TorusData` and use its names; copy verbatim (T13 copy policy, delimited blocks with source-line markers, own namespaces `BlowupDensity.T10.Draft` /
  `BlowupDensity.T11.Spec` / `BlowupDensity.T12.Spec`) only the still-unregistered T10 solution-class declarations, the T11 declarations you use (`SolvesBelowT`, `IsMaximalPeriodicSolution`,
  `galileanMeanT`, `PeriodicMeanReductionAPI` if cited), and the T12 vocabulary (`IsPeriodicLambda`, `SmoothPeriodicT`, `MemPeriodicHomogeneous`, `periodicLpENorm`, `gradientTensor`, `laplacian`);
  where a registered Section 4 twin exists (`gradientSq`/`laplacianSq`/`l2Sq` in `Contracts/V1/GradientL6.lean`/`Data.lean`, `C01.enstrophyIdentity` shape in `Contracts/V4/EnergyAbsorption.lean`),
  check the spelling with `example … := rfl`.
- **Structure and fields exactly as `research/T20/RECONCILIATION.md` §3**: one Type-valued `CriticalRegularityTAPI` (constants/shrinking parameters as data fields first, then the eleven theorem
  fields in the §3 order, incl. the two `:411` fields and the `:492-500` continuation display; the main field `globalRegularity` concluding `maximalLifespanT ν 0 g = ⊤` from `eq:smallcritical`);
  no API indices; the mean-free reduction objects as `def`s; every field with the exact `MemLp`/class/integrability guards the reconciliation prescribes (no junk-value traps), the constant `c`
  fixed before `ν, g`.
- Report the elaboration of `research/T20/Spec.lean` and the `rfl` checks; do not prove anything.

## Field checklist (added after a rejected first run)
A previous run delivered a `Spec.lean` that was Draft A with a new header (9 fields, no `rfl` checks). **That is not the reconciled spec and was discarded.** The reconciled
`CriticalRegularityTAPI` must have **exactly** these fields, in this order, with the constant/shrinking-parameter data fields first as `research/T20/RECONCILIATION.md` §3 prescribes:
`c` (+ its positivity), `reductionRegular`, `meanBound`, `meanFreeEquation`, `constantTransportSkew`, `constantTransportCommutesLambda`, `criticalEnergy`, `bIntegral`, `yBound`, `hOneEnergy`,
`continuationBound`, `globalRegularity` — each spelled per the §2 rulings (Draft B's `ClassicalSolutionT`-shaped interval estimates, A's real `∫‖·‖²` spellings, `MemLp` guards, no API indices).
Your report must include the list of your structure's fields and confirm it equals this list; include the `example … := rfl` checks against the registered spellings the reconciliation names.
