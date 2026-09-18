# Lane 378 — T19 density package, reconciled specification (Opus prover; transcribed by the lead from the agent's final message — report-file guard)

Commit `7f48786787723fb3030eb1d93e63b291174b9dbf` on `erenup/378-SPEC-t19-spec`.

## 1. What was stated
`research/T19/Spec.lean` (namespace `BlowupDensity.T19`), per `RECONCILIATION.md` §3 (bases B/B/A/A, all `Prop`, T18 record not threaded, no honesty guards, registered `alpha`, `𝓧` topology by fixing `a`): four `Prop` structures, 13 fields — `PeriodicDensityAPI` (3: `fixedInitialDensity`, `thresholdValue : criticalOrder 1 = 1/2`, `regularReferenceSingular`), `MixedRegionAPI` (3: `mixedDensity` via `RelativelyDenseMixedT`, `mixedRegionArithmetic` on registered `alpha`, `regionExamples` = `0 < alpha 2 1 ∧ 0 < alpha (4/3) 2`), `StrongClosureAPI` (4: `energyTimeEmbedding`, `closureInEnergy`, `simultaneousPairConvergence`, `referenceFiniteEnergy`), `ProjectionAPI` (3: `extendedProductDensity`, `projectionOntoInitialData` = `Prod.fst '' 𝔅 = initialClassT`, `zeroInitialProjection` = `{0}`); four `…Statement` defs in the paper's quantifier order; helpers `RegularTrajectoryT`, `SingularTrajectoryT`, `extendedBreakdownSetT`, `spaceTimeL2L2ENormT`, `RelativelyDenseMixedT`; carriers `IsPeriodicLebesgueSlicePath`, `mixedLebesgueENormT` copied verbatim from `research/T18/Spec.lean:395-410`. Docstrings cite the current `03-torus.tex` lines (`:350`, `:363-365`, `:535-538`, `:543-560`, `:570-579`, `:586`, `:590`).

## 2. Files
`research/T19/Spec.lean`, `research/T19/COMPARISON.md` (clause → field table with A/B provenance and R41/R46 counterparts; proof dependencies; five owner questions); provenance copies `DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_367.md`, `REPORT_372.md`.

## 3. Deviations
None of substance. Citation retiming done (`:579/:586/:590`, threshold at `:350`); the two carrier docstrings keep their verbatim `:129-133` citation; no `rfl` drift examples (nothing copied overlaps a registered name; `alphaT` dropped for the registered `alpha`).

## 4. Commands and results
`lake env lean ../research/T19/Spec.lean` → exit 0, no output; stub grep and `sorry|admit|native_decide|axiom` grep empty; field counts 3/3/4/3 confirmed; tree clean.
