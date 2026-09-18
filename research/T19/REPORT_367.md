# Lane 367 — T19 density package, double-blind draft A (Opus prover; report transcribed by the lead from the agent's final message — report-file guard)

Commit `88274ae09fc5eb301969c8438f067172cbced1d6` on `erenup/367-SPEC-t19-draft-a`.

## 1. What was stated
Four `Prop`-valued structures (one field per statement/proof clause, paper lines, quantifier order, non-vacuity notes) + one `def …Statement : Prop` each, in `research/T19/DraftA.lean` (553 lines):
- `prop:density` (`:349-382`) → `PeriodicDensityAPI` (3 fields): `density` = `RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)` for `s < 1/2`; `alreadySingularApprox` (`T_max ≤ T`, `f = g`); `regularReferenceApprox` (`T_max > T`: one inserted family `g_ε`, lifespan exactly `T`, `L¹_tH^s` closeness for `0 ≤ s < 1/2` and `s < 0`); `periodicDensityStatement`.
- `cor:mixed` (`:528-539`) → `MixedRegionAPI` (4 fields): `mixedRegionArithmetic` (`3/p + 2/q > 3 → α(p,q) > 0 ∧ α(p,q) + 1 > 0`), `mixedDensity`, `alreadySingularMixedApprox`, `regularReferenceMixedApprox` (`eq:Fclose → 0`); `mixedRegionStatement`.
- `cor:closure` (`:540-563`) → `StrongClosureAPI` (3 fields): `energyTimeEmbedding` (`‖z‖_{L²_tL²} ≤ √T ‖z‖_{L^∞_tL²}`), `closureInEnergy`, `simultaneousPairConvergence`; `strongClosureStatement`.
- `prop:projection` (`:564-631`) → `ProjectionAPI` (3 fields): `extendedProductDensity`, `projectionOntoInitialData` (`Prod.fst '' 𝔅_{ν,T} = 𝓧`), `zeroInitialProjection`; `projectionStatement`.
All `Prop`-valued (pure `∀∃` claims; constants live in T18/T20). Imports registered `Contracts.V1.{TorusLocalTheory, MaximalPartial, Correction, MainThresholds, CompletedDensity}`; copies verbatim the four unregistered carriers `IsPeriodicLebesgueSlicePath`, `mixedLebesgueENormT`, `MemMixedLebesgueT`, `MemForceSobolevT` (`research/T18/Spec.lean:396-433`); defines `RegularTrajectoryT`/`SingularTrajectoryT`, `extendedBreakdownSetT`, `spaceTimeL2L2ENormT`.

## 2. Files
`research/T19/DraftA.lean`; `research/T19/COMPARISON_A.md` (clause → field table with Section 4 counterparts, five ambiguities, needs-a-lemma list, Paper1 candidates).

## 3. Gaps / modelling choices to settle at reconciliation
- T18's `PeriodicInsertionAPI` deliberately **not** copied: the regular-reference fields name the *conclusions* of `thm:insertion` in registered vocabulary (mirroring `MainThresholdsAPI.regularReferenceApproximation` / `CompletedDensityAPI.strongTrajectoryClosure`) rather than producing the insertion record; draft B may thread it instead.
- Density and `cor:closure` rendered as ε-approximation (`RelativelyDenseT`), not topological closure (no `TopologicalSpace` on force space is registered).
- `prop:projection`'s "any topology on X" discharged by keeping the initial datum fixed at `a`.

## 4. Commands and results
`lake env lean ../research/T19/DraftA.lean` → exit 0, no output; stub grep (`: *True|:= *0$|→ *True`) empty; `sorry|admit|native_decide|axiom` grep empty (docstring words reworded).
