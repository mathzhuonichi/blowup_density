# Lane 372 — T19 density package, double-blind draft B — report

## 1. What was stated (statements only, no proofs)

Draft B of the Lean statements of the four Section 3 density results,
`paper/sections/03-torus.tex:349-631`, in namespace `BlowupDensity.T19.DraftB`
(file `research/T19/DraftB.lean`). One `Prop`-valued structure per result; each
field is one clause of the paper's statement/proof, with paper-line docstring,
exact quantifier order, and a non-vacuity note.

- **`PeriodicDensityAPI` (`prop:density`, `:349-361`) — 3 fields:**
  `fixedInitialDensity` (`RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)`
  for `s<1/2`), `thresholdValue` (`criticalOrder 1 = 1/2`),
  `regularReferenceSingular` (exact-`T` singular force near every reference
  regular through `T`, the `:626-631` distinction).
- **`MixedRegionAPI` (`cor:mixed`, `:528-539`) — 3 fields:** `mixedDensity`
  (`RelativelyDenseMixedT q p …` on the region `3/p+2/q>3`), `regionPositive`
  (`α(p,q)>0 ∧ α+1>0`), `regionExamples` (the two named spaces `L¹_tL²_x`,
  `L²_tL^{4/3}_x`).
- **`StrongClosureAPI` (`cor:closure`, `:540-563`) — 2 fields:** `strongClosure`
  (one existential family: per-`ε` torus force, exact lifespan `=ofReal T`,
  finite `E_T`, a `ClassicalSolutionT` with pinned velocity and history; the
  `energyENormT` limit; and the simultaneous `∀s<1/2` `forceSobolevENormT 1 s`
  limit — all along `𝓝[>]0`), `referenceFiniteEnergy` (reference has finite
  `E_T`).
- **`ProjectionAPI` (`prop:projection`, `:564-631`) — 3 fields:** `productDensity`
  (density of the pair set `𝔅_{ν,T}` in `𝓧×𝓕`), `projectionOntoInitial` (`∀a∃f`
  onto all of `𝓧`), `zeroInitialFiber` (`a=0` fibre projects to `{0}`).

Plus 4 headline `def …Statement : Prop` in the paper's quantifier order, and the
helper `def RelativelyDenseMixedT` (mixed-Lebesgue analogue of registered
`RelativelyDenseT`).  Structures are `Prop`-valued because none of the four
results introduces a constant or datum (constructed forces/families are bound
existentially inside a field).

## 2. What exists in Lean now

`research/T19/DraftB.lean` (465 lines): elaborates with `lake env lean`, 0
errors, no `sorry`/`admit`/`axiom`/`native_decide`, no `: True`/`:= 0`/`→ True`.

- Registered imports used by name: `Contracts.V1.TorusData`,
  `Contracts.V1.TorusLocalTheory`, `Contracts.V1.CompletedDensity`,
  `Contracts.V1.MainThresholds`.
- Copied verbatim (namespace `BlowupDensity.T15.Draft`) from
  `research/T18/Spec.lean:395-442`: `IsPeriodicLebesgueSlicePath`,
  `mixedLebesgueENormT`, `alphaT`, with an `example … := rfl` drift check
  `alphaT = BlowupDensity.Contracts.V1.alpha`.
- `research/T19/COMPARISON_B.md`: clause→field table for all four results with
  Section 4 counterpart column, design choices, six reconciliation ambiguities,
  the "needs a lemma" list, and `Paper1/` implementation candidates.

## 3. Gap

- Statement-only: no proofs, no binding, no registration; reconciliation with
  draft A pending (six ambiguities in `COMPARISON_B.md`).
- Two clauses stated operationally, not literally: `eq:closure`'s set-inclusion
  (stated as existence of `E_T`-convergent exact-`T` approximants) and the
  `prop:projection` `{0}`-non-density remark `:619-622` (paper leaves the `𝓧`
  topology generic). The `cor:closure` norm-equivalence `:552-560` is a
  proof-side Bochner lemma, not a field.
- No T20 (`prop:critical`) vocabulary: the density package is constructive
  (proofs consume `thm:insertion` = T18) and does not consume `prop:critical`.

## 4. Commands run and results

- `cd verification && lake env lean ../research/T19/DraftB.lean` → exit 0
  (elaboration gate, clean).
- `grep -nE ': *True|:= *0$|→ *True' research/T19/DraftB.lean` → empty (rc=1).
- `grep -nE '\b(sorry|admit|native_decide)\b|axiom ' research/T19/DraftB.lean`
  → empty (rc=1).
- Field counts: PeriodicDensityAPI 3, MixedRegionAPI 3, StrongClosureAPI 2,
  ProjectionAPI 3; + 4 `…Statement` defs + `RelativelyDenseMixedT` + 3 copied
  vocab defs + 1 drift `example`.
