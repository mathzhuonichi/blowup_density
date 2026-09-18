# Lane 382 — T23 `cor:boundary`, reconciled specification (Opus prover; transcribed by the lead from the agent's final message — report-file guard)

Commit `746f645e3021c77a242a22cb15de499b18871f6f` on `erenup/382-SPEC-t23-spec`.

## 1. What was stated
`research/T23/Spec.lean` (namespace `BlowupDensity.T23.Spec`), per `RECONCILIATION.md` §3 (base B + three imports from A): `structure BoundaryInsertionAPI … : Type` (48 fields = B's 47 + the record-form `maximal : IsMaximalDomainSolution …`), `def boundaryInsertionStatement : Prop` (domain/geometry, `ν`, `(a,g,r,δ)`, the reference, then `Nonempty`); supporting `DomainPlacementData` (16 fields, **cube-free**: no `fundamentalCube`, support at the free `x₀`, domain containment via the API field `interiorBall_in_domain`), `ClassicalSolutionOmega` (10), `IsBoundedBoxOrSmoothDomain` (`IsBoxDomain ∨ IsRegularLevelDomain`, with `Ω.Nonempty` folded in), `BoundedDomainNormAPI` copied from T22; the registered whole-space `ScalingAPI`/`CorrectionAPI` are consumed, not threaded; only `norms` and `reference` are threaded. Imports only registered contracts + `Contracts.V2.InsertionLifespan`; copied unregistered vocabulary: T16.Draft `correctedBackground`/`CutoffData`, T17.Spec `correctionForce`, all of `research/T22/Spec.lean`. `Paper1/BoundaryCorollary.lean` (sorry at `:90`) cited only. Five `rfl` drift examples pin the registered names used.

## 2. Files
`research/T23/Spec.lean`; `research/T23/COMPARISON.md` (clause → field table with A/B provenance and T18 counterparts; proof dependencies; owner questions); provenance `DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_368.md` (no `REPORT_374.md` existed on the B branch).

## 3. Gaps / deviations
Specification only. Assembly must consume T22's `BoundedDomainNormAPI` (`orderZero`/`cutoffMultiplier`/`zeroExtensionComparison`), the registered whole-space `ScalingAPI`/`CorrectionAPI`, and a T11 bounded-domain local theory (`prop:local` on Ω) — none registered yet. Deviations: none substantive (`Ω.Nonempty` folded into the domain predicate; drift examples as house style).

## 4. Commands and results
`lake env lean ../research/T23/Spec.lean` → exit 0, 0 errors (twice); stub grep empty; `sorry|admit|axiom|native_decide` only in prose; field counts 16 / 10 / 48.
