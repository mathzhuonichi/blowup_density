# R43 draft A — comparison and clause gaps

Proposition 4.3 (`prop:Rcritical1`, "Global regularity for small critical data
and `L¹` force"), `paper/sections/04-whole-space.tex:82-133`. Structure
`BlowupDensity.R43.DraftA.CriticalRegularityL1API` in `research/R43/DraftA.lean`.
Ledger §3, `research/section4/STATEMENTS.md:428-556`.

Typecheck: `cd verification && lake env lean ../research/R43/DraftA.lean` → exit
0, no errors, no warnings. No `sorry`/`axiom`/`native_decide`/placeholder-`Prop`
field.

The centrepiece is the two consequence fields `universal` and
`inhomogeneousAtZero` (the clean ledger skeleton, `:502-518`), which is all
`R41` consumes (`:128-135`). The remaining fields restate, as `⟪Source:field⟫`
hypotheses, the sibling-API clauses R43's proof passes through — following the
`research/A02/Spec.lean` precedent that restates its `⟪A01:…⟫` clauses verbatim
because the drafts are not importable.

## 1. Field table

| field | paper line | consumed from | existing Lean (formalization / vendor) | gap |
|---|---|---|---|---|
| `c`, `hc` | `04:83` | — (universal constant) | pattern: `A05 CriticalEmbeddingAPI.C/Cpos` | none |
| `Cemb`, `hCemb` | `appx-B:14-15`, `04:93` | ⟪A05:C (1/2)⟫ | `Source/RieszPotentialLp.lean:14 targetExponent` (exponent only) | A05 unregistered |
| `universal` | `04:84-87` | — (the theorem) | **none** — no small-data global regularity in tree; `vendor/…/ModulatedStockBounds.lean:167` is an unrelated angular bound | whole theorem is new |
| `inhomogeneousAtZero` | `04:88,132` | — (the theorem, `a=0`) | none | new; reduces to `universal` via `‖·‖_{Ḣ^{1/2}} ≤ ‖·‖_{H^{1/2}}` |
| `existsMaximal` | `02-prelim:105` | ⟪A02:exists_maximal⟫ (`research/A02/Spec.lean:421`) | model `Source/SmoothLifespan.lean:41 lifespan` + `Flow` existence | A02 unregistered; on `maximalLifespanR`/`ClassicalSolutionR` |
| `lifespanLeIffNoExtension` | `02-prelim:32,105`; `04:131` | ⟪A02:lifespan_le_iff_no_extension⟫ (`research/A02/Spec.lean:451`) | `Source/SmoothLifespan.lean:58 lifespan_le_iff_no_extension` (proved for `Flow`) | A02 restates it on `maximalLifespanR`; unregistered |
| `continuation` | `02-prelim:105-110`, `appx-A:127-157`, `eq:criterion` | ⟪A04:continuation (eq:criterion)⟫ | **none** — no `H²`-time-integral continuation criterion in tree (`Source/LocalizedBlowup.lean:36 no_continuous_continuation` is the `L^∞` blowup form, a different clause) | **A04 spec does not exist** |
| `velocityCriticalL3` | `appx-B:29`, `04:93` | ⟪A05:velocityCriticalL3⟫ (`research/A05/Spec.lean:366`) | partial: `Source/RieszPotentialLp.lean` Riesz `L^p`; A05 `COMPARISON` covers | A05 unregistered; uses A05-local `dotHomogeneousENorm` |
| `criticalNormBound` (`y ≤ cν`) | `04:97-104`, `eq:Rcritical1` | R43 core (uses A05 `velocityCriticalL3`+`derivativeCriticalL3`) | `vendor/…/R3/ScalarEnergyBound.lean forced_gronwall(_weighted/_uniform)`, `vendor/…/R3/ComparisonGronwall.lean` | the `½(y²)'+(ν−C₀y)z² ≤ by` ODE, regularised norm division, first-exit/continuity bootstrap — none specialised in tree |
| `velocityL3Small` (`‖u‖₃ ≤ Cemb·cν`) | `04:93,97-104` | R43 core (`velocityCriticalL3` ∘ `criticalNormBound`) | none | derived; whole-space analogue of `04:157` `‖u‖₃ ≤ Cθν` |
| `h2SquaredIntegralFinite` (`∫₀^S ‖u‖²_{H²}<∞`) | `04:118-131` | ⟪C01:h2TimeIntegral⟫ | partial: `Source/PacketEnergy.lean:35 pde_energy_inequality` (an energy identity); vendor `forced_gronwall` | **C01 spec does not exist**; needs `eq:RL2`+`eq:RH1`+`H²` Fourier inequality assembled |

## 2. `Data.lean` object choices (and one gap)

* `X_R = initialClassR` (`Data.lean:509`); `F_R = MemForceR` (`:544`);
  `T^ν_{max,R} = maximalLifespanR` (`:657`); `ClassicalSolutionR` (`:624`).
* Force norms are Data.lean, datum-based (faithful): `‖f‖_{L¹(0,∞;Ḣ^{1/2})} =
  forceHomogeneousENorm 1 (1/2) f` (`:390`); `‖f‖_{L¹(0,∞;H^{1/2})} =
  forceSobolevENormL1 (1/2) f` (`:231`). `H²` slice norm `sobolevENorm 2`
  (`:189`), datum-based.
* **Gap — the spatial `Ḣ^{1/2}` norm.** Data.lean's `dotHHalfENorm` (`:427`) is
  an abbreviation of `homogeneousFourierENorm` (`:410`), a **literal pointwise
  Fourier integral** whose own docstring (`:401-419`) forbids its use on a
  general `H^∞` slice, where `angularFourier` returns a **junk `0`** for a
  field that is not `L¹`. `X_R = H^∞ ∩ L²_σ` contains non-`L¹` fields (e.g.
  smooth `∼|x|^{-2}` decay), so using `dotHHalfENorm a` in the smallness
  hypothesis would let a **large-data** `a` satisfy the smallness *vacuously*
  (`0 < cν`), and the conclusion `T_max = ∞` could then be false — a hypothesis
  a wrong implementation could satisfy. Draft A therefore uses the
  **datum-infimum** form `dotHomogeneousENorm (1/2) a` (verbatim copy of
  `research/A05/Spec.lean:131`), which fails safe to `⊤` and equals the true
  `‖a‖_{Ḣ^{1/2}}` on `X_R`. This matches the *force* side (already datum-based)
  and matches what A05 uses on the right of `velocityCriticalL3`.
  **Recommendation for D01:** register a datum-infimum spatial `‖·‖_{Ḣ^s}` on
  `SpatialField` (A05 `dotHomogeneousENorm`), and mark `dotHHalfENorm`/
  `dotHThreeHalvesENorm` as "quantity forms, `L¹∩L²` slices only".

Local copies in `DraftA.lean` (each verbatim, with provenance): `dotHomogeneousENorm`
(A05), `IsMaximalSolution` and `presingularTimes` (A02). These vanish into
imported-API fields once A05/A02 register.

## 3. Bounded unit split (proof of `CriticalRegularityL1API`, ≤8 units)

| unit | size | content | consumes |
|---|---|---|---|
| U1 | S | `inhomogeneousAtZero` from `universal`: `‖f‖_{Ḣ^{1/2}} ≤ ‖f‖_{H^{1/2}}` (D01 monotonicity, `constant 1`) and `‖0‖_{Ḣ^{1/2}} = 0` | D01 `Hs` monotonicity |
| U2 | L | `criticalNormBound`: `eq:Rcritical1` energy identity against `Λu`, regularised division `(y²+ζ²)^{1/2},ζ↓0`, first-exit/continuity bootstrap on `{y ≤ ν/(2C₀)}`, `c<1/(4C₀)` | A05 `velocityCriticalL3`+`derivativeCriticalL3`; vendor Gronwall; a reusable regularised-division lemma |
| U3 | S | `velocityL3Small`: compose `velocityCriticalL3` with `criticalNormBound` in `ℝ≥0∞` | U2 |
| U4 | M | `h2SquaredIntegralFinite`: `eq:RL2`+`eq:RH1`+`H²` Fourier inequality assembled at finite `S ≤ T_max` | **C01** (all three); A05 `gradientLSix`; U3 (for `C₁y ≤ ν/4`) |
| U5 | S | `continuation`: `eq:criterion` on the maximal solution | **A04** |
| U6 | M | `universal`: exclude finite `T_max` — from `existsMaximal`, `h2SquaredIntegralFinite`, `continuation`, `lifespanLeIffNoExtension` derive `= ⊤` | U4, U5, A02 |
| U7 | S | `existsMaximal`, `lifespanLeIffNoExtension` | **A02** |
| U8 | M | norm bridges: `dotHomogeneousENorm` faithful on `X_R`; `forceHomogeneousENorm` datum path exists for `F_R`; `sobolevENorm 2` slice measurability for the `∫⁻` | D01, A05 |

## 4. Clauses R43 needs that A04 / C01 do NOT currently provide (most valuable output)

`A04` and `C01` **have no spec in this worktree at all**, so every clause R43
consumes from them is currently unprovided. The exact shapes R43 needs — the
first written statement of each — are:

**A04 (`ContinuationAPI`) must export:**

1. **`continuation` = `eq:criterion` in extension form.** Exactly the field
   `CriticalRegularityL1API.continuation`:
   for `0 < ν`, `a ∈ X_R`, `f ∈ F_R`, `0 < S`, and any
   `w : ClassicalSolutionR ν a f S`,
   `(∫₀^S ‖w.velocity(t)‖²_{H²} dt < ∞) → ENNReal.ofReal S < maximalLifespanR ν a f`.
   The paper states it as "extends smoothly beyond `S`" (`02-prelim:108`); R43
   needs the `maximalLifespanR`-level consequence, not merely a longer solution,
   so that it chains with A02's `lifespanLeIffNoExtension`. The in-tree
   `no_continuous_continuation` is the `L^∞`-blowup form and is **not** this
   clause.

**C01 (`EnergyAbsorptionAPI`) must export:**

2. **`h2TimeIntegral` — the assembled finiteness**, not just `eq:RL2`/`eq:RH1`
   separately. Exactly `CriticalRegularityL1API.h2SquaredIntegralFinite`: along
   the *maximal* solution `(u,p)` (`IsMaximalSolution`) of small critical data,
   for every finite `S` with `ENNReal.ofReal S ≤ maximalLifespanR ν a f`,
   `∫₀^S ‖u(t)‖²_{H²} dt < ∞`. R43 consumes the assembly (`04:127-131`), so C01
   must publish it *pre-assembled and lifespan-wide*; publishing only the two
   ODEs `eq:RL2`/`eq:RH1` would push the `H²` Fourier inequality
   `‖u‖²_{H²} ≤ C(‖u‖₂²+‖Δu‖₂²)` and the `∫⁻`-assembly into R43.
3. **The estimates must be stated on the maximal solution at presingular
   times**, i.e. quantified as `∀ (u,p), IsMaximalSolution ν a f u p → ∀ t ∈
   presingularTimes …` (or over every `ClassicalSolutionR ν a f S`, `S ≤
   T_max`). A C01 that fixes one horizon `T` cannot feed R43's "every finite `S`
   within or at `T_max`" (`04:121`).
4. **`eq:RH1`'s smallness gate `C₁‖u‖₃ ≤ ν/4` must be the same `ν`-scaled
   smallness R43 provides** (`velocityL3Small`, `‖u‖₃ ≤ Cemb·cν`). C01 should
   take the `‖u‖₃`-smallness as a hypothesis in the shape R43 supplies, so the
   two constants (`C₁`, `Cemb`, `c`) compose without a `ν`-dependent `c`.

**Already provided (used but not gaps):** A02 `exists_maximal`,
`lifespan_le_iff_no_extension` (drafted, `research/A02/Spec.lean:421,451`; model
proved in `Source/SmoothLifespan.lean:58` for `Flow`); A05 `velocityCriticalL3`,
`derivativeCriticalL3`, `gradientLSix` (drafted, `research/A05/Spec.lean:366-402`).
Both still need registration under `verification/Contracts/` before R43's
binding can `import` them; until then R43's fields are the restated copies.

**Cross-cutting requirement for A05/D01:** the spatial `Ḣ^{1/2}` and `Ḣ^{3/2}`
quantities R43 and C01 estimate live on `SpatialField` and must be the
**datum-infimum** form (A05 `dotHomogeneousENorm`), not Data.lean's
`dotHHalfENorm` (§2 gap). Whichever module owns it, all of R43/C01/A05 must
share the one faithful definition.
