# T19 — merged paper-clause → Lean-field comparison (reconciled spec)

Node T19 = the density package on `T³`: `prop:density` (`03-torus.tex:349-368`),
`cor:mixed` (`:528-538`), `cor:closure` (`:540-561`), `prop:projection`
(`:564-590`).  File `research/T19/Spec.lean`, namespace `BlowupDensity.T19`,
elaborates with 0 errors (`cd verification && lake env lean ../research/T19/Spec.lean`).

Reconciled from the two double-blind drafts (`DraftA.lean` lane 367,
`DraftB.lean` lane 372) under `RECONCILIATION.md`.  Per-structure bases:
`PeriodicDensityAPI` → **B**, `MixedRegionAPI` → **B**, `StrongClosureAPI` → **A**,
`ProjectionAPI` → **A**.  All four structures `Prop`-valued (data-free; every
family bound existentially inside a field).  Four future contract ids:
`T19.periodic_density`, `T19.mixed_region`, `T19.strong_closure`, `T19.projection`.

Registered vocabulary imported and used by name (never copied): `RelativelyDenseT`,
`breakdownSetT`, `forceClassT`, `initialClassT`, `maximalLifespanT`,
`RegularThroughT`, `ClassicalSolutionT`, `energyENormT`, `energyEssSupT`,
`forceSobolevENormT` (`Contracts/V1/TorusLocalTheory.lean`); `criticalOrder`
(`.Data`); `BlowupDensity.Contracts.V1.alpha` (`.Correction`);
`MaximalPartial.{limsupLeft,speedENorm}` (`.MaximalPartial`).  Copied verbatim
into `BlowupDensity.T15.Draft` from `research/T18/Spec.lean:395-410`: only
`IsPeriodicLebesgueSlicePath`, `mixedLebesgueENormT` (no `alphaT`, no honesty
guards).  Local restatements over registered vocabulary: `RegularTrajectoryT`,
`SingularTrajectoryT`, `extendedBreakdownSetT`, `spaceTimeL2L2ENormT` (A),
`RelativelyDenseMixedT` (B).

R41 = `MainThresholdsAPI` (`Contracts/V1/MainThresholds.lean`);
R46 = `CompletedDensityAPI` (`Contracts/V1/CompletedDensity.lean`).

---

## 1. `prop:density` → `PeriodicDensityAPI` (`Prop`, 3 fields) — base B

| Paper clause (`03-torus.tex`) | draft A field | draft B field | Lean field (reconciled) | R41/R46 counterpart | ruling (reason) |
|---|---|---|---|---|---|
| Statement `:350-355` `∀g∀ρ∃f: ‖f-g‖_{L¹_tH^s}<ρ ∧ T_max≤T`, `s<1/2` | `density` | `fixedInitialDensity` | `fixedInitialDensity` = `RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)` | R41 `fixedInitialDensity` (`q∈{1,2}`) | **both, identical.** Kept verbatim; torus fixes `q=1`. |
| threshold `:350` `s<1/2` | docstring only | `thresholdValue` (field) | `thresholdValue : criticalOrder 1 = 1/2` | R41 `thresholdValues` | **B.** Field pins the torus threshold to R41's arithmetic; cheap honest real equality. |
| already-singular case `:360-361` (`T_max≤T`, `f=g`) | `alreadySingularApprox` | folded into proof | (dropped) | folded into R41 proof | **B (drop A's field).** `f=g` with `‖0‖=0<r` is a proof case, not a statement clause. |
| regular-reference exactly-`T` `:363-365`,`:590` | `regularReferenceApprox` (family, split `0≤s<1/2`/`s<0`, `MemForceSobolevT` guards) | `regularReferenceSingular` (per-`(s,r)` strict `<r`, hyp `RegularThroughT`) | `regularReferenceSingular` | R41 `regularReferenceApproximation` | **B.** Per-`(s,r)` strict-`<r` form states exactly "near every reference regular through `T`, ∃ nearby force with lifespan exactly `T`"; self-guarding, registered `RegularThroughT`, no `s`-range split, no honesty guard. A's family+energy content is `cor:closure`'s job. |

`def periodicDensityStatement` = the `fixedInitialDensity` field, paper order `a,ν,T,s`.

## 2. `cor:mixed` → `MixedRegionAPI` (`Prop`, 3 fields) — base B

| Paper clause | draft A field | draft B field | Lean field (reconciled) | R41/R46 counterpart | ruling (reason) |
|---|---|---|---|---|---|
| Statement `:529-531` `eq:mixedregion` density in `L^q_tL^p_x` | `mixedDensity` (inlined `∃f∈𝓑, …<r`) | `mixedDensity` (`RelativelyDenseMixedT`) | `mixedDensity` (`RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)`) | torus-only | **B.** `RelativelyDenseMixedT` is the exact mixed-norm analogue of registered `RelativelyDenseT`; one binding site, parallel to the Sobolev statement. |
| arithmetic driver `:535-536` `α>0` hence `α+1>0` | `mixedRegionArithmetic` (**registered** `alpha`) | `regionPositive` (copied `alphaT`) | `mixedRegionArithmetic` (registered `alpha`) | R41 `thresholdValues` (analogue) | **A's spelling on B's field.** Registered `Contracts.V1.alpha` used directly; B's `alphaT` copy + drift `example` dropped. Content identical. |
| named spaces `:538` `L¹_tL²_x`, `L²_tL^{4/3}_x` | absent | `regionExamples` (real literals) | `regionExamples` (`0<alpha 2 1 ∧ 0<alpha (4/3) 2`) | torus-only | **B, retimed to registered exponent.** Stated at `ℝ≥0∞` points so it instantiates the region predicate (`α(2,1)=1/2>0`, `α(4/3,2)=1/4>0`). |
| already-singular / regular-reference **mixed** cases | `alreadySingularMixedApprox`, `regularReferenceMixedApprox` (`MemMixedLebesgueT`) | absent | (dropped) | — | **drop both (A).** Proof says "use the same two cases as in `prop:density`" (`:535`); re-articulating in the mixed norm is redundant. Dropping removes the only need for `MemMixedLebesgueT`. |

`def mixedRegionStatement` = the `mixedDensity` field, paper order.

## 3. `cor:closure` → `StrongClosureAPI` (`Prop`, 4 fields) — base A

| Paper clause | draft A field | draft B field | Lean field (reconciled) | R41/R46 counterpart | ruling (reason) |
|---|---|---|---|---|---|
| norm-equivalence `:556-560` `‖z‖_{L²_tL²} ≤ T^{1/2}‖z‖_{L^∞_tL²}` | `energyTimeEmbedding` | deferred to proof-side lemma | `energyTimeEmbedding` (`spaceTimeL2L2ENormT T z ≤ ofReal(√T)·energyEssSupT T z`) | torus-only | **A.** A displayed inequality (`:559`), TRUE in `ℝ≥0∞`, self-contained; documents the `E_T ↔ L²_tH¹` reading `eq:closure` relies on. |
| `eq:closure` set inclusion `:543-545` `R_{a,T}⊆S̄_{a,T}^{E_T}` | `closureInEnergy` (ε-approx over `R`/`S`) | operational only | `closureInEnergy` (with `RegularTrajectoryT`/`SingularTrajectoryT`) | torus-only | **A.** `eq:closure` check is literal; `R`/`S` (`:541-542`) rendered over registered `ClassicalSolutionT`; `⊆ closure^{E_T}` as ε-approximation. |
| simultaneous pair convergence `:546-549` | `simultaneousPairConvergence` (family, `E_T` limit, `∀s<1/2` `L¹_tH^s` limit, per-`ε` `SingularTrajectoryT`) | `strongClosure` (+ `energyENormT<⊤`, pinned velocity, **history on `[0,T−2ε²]`**) | `simultaneousPairConvergence` (A, minus B's history) | R46 `strongTrajectoryClosure` | **A, minus history.** A mirrors R46's shape (family, exact lifespan, solution, two `Tendsto` along `𝓝[>]0`). R46 carries no `history`; drop B's `history` (a `thm:insertion` detail). Keep A's `SingularTrajectoryT (u ε)`. |
| reference finite `E_T` `:554` | implied by `S`/`R` | `referenceFiniteEnergy` (field) | `referenceFiniteEnergy : energyENormT T reference.velocity < ⊤` | implicit in R46 | **B (add as 4th field).** Anchors the `E_T` limit in a finite-distance ambient space; cheap, honest. |

`def strongClosureStatement` = the `closureInEnergy` field (`eq:closure`).

`RegularTrajectoryT`/`SingularTrajectoryT` render `R`/`S`; "unbounded max speed
at `T`" = `MaximalPartial.limsupLeft T (t↦speedENorm(u(t,·)))=⊤`; "finite `E_T`"
= `energyENormT T u ≠ ⊤`; "smooth on `[0,T)`" = a `ClassicalSolutionT` on horizon
`T` (smooth on `Ico 0 T`).

## 4. `prop:projection` → `ProjectionAPI` (`Prop`, 3 fields) — base A

| Paper clause | draft A field | draft B field | Lean field (reconciled) | R41/R46 counterpart | ruling (reason) |
|---|---|---|---|---|---|
| product density `:570,573-575` (keep `a` fixed) | `extendedProductDensity` (`(a,f)∈𝔅 ∧ …<r`) | `productDensity` (component form) | `extendedProductDensity` (with `extendedBreakdownSetT`) | torus-only | **A.** Uses the defined pair set `𝔅 = extendedBreakdownSetT`, making density of the *pair* set explicit; `a` kept fixed discharges "any topology on `𝓧`". |
| projection onto `𝓧` = all of `𝓧` `:570,579` | `projectionOntoInitialData : Prod.fst '' 𝔅 = initialClassT` | `projectionOntoInitial : ∀a∈𝓧, ∃f∈𝓕, T_max≤T` | `projectionOntoInitialData` (`= initialClassT`) | torus-only | **A.** The literal `Prod.fst '' 𝔅 = 𝓧`; `⊆` by construction, `⊇` the genuine `∀a∃f` content. B states only the `⊇` half operationally. |
| `a=0` fibre `:571` → `{0}` | `zeroInitialProjection : Prod.fst '' {p∈𝔅∣p.1=0} = {0}` | `zeroInitialFiber : 0∈𝓧 ∧ ∃f∈𝓕, T_max^ν(0,f)≤T` | `zeroInitialProjection` (`= {0}`) | torus-only | **A.** The literal `= {0}`; `⊇` forces the `a=0` fibre nonempty, so the singleton is inhabited, not `∅`. |
| `:586` "`{0}` not dense in nontrivial normed `𝓧`" | omitted | omitted | **omitted** (both) | — | **omit from both (justified).** Needs an abstract normed topology on `𝓧`, which the paper leaves generic; no registered `𝓧` topology exists. Captured operationally by the `∀a∃f` order + `zeroInitialProjection`. Owner question §5. |

`def projectionStatement` = product-density (force factor) ∧ full projection,
paper order `ν,T`.  `𝔅_{ν,T}` = `extendedBreakdownSetT ν T ⊆ 𝓧×𝓕`.

---

## Proof dependencies (copied from `RECONCILIATION.md` §4)

The spec lane writes only the statement; the assembly lane consumes:

- **`fixedInitialDensity` / `regularReferenceSingular`:** the dichotomy
  `le_or_lt (maximalLifespanT ν a g) (ofReal T)` (Mathlib); already-singular
  branch → `forceSobolevENormT 1 s 0 = 0 < r` (`eLpNorm` of the zero field);
  regular branch → T18 `PeriodicInsertionAPI.{lifespan (=ofReal T), force_mem,
  forceDifference_sobolev_bound (0≤s<1/2), forceDifference_negativeSobolev_tendsto
  (s<0)}`, with the reference solution from `RegularThroughT ν a g T`
  (T11 / registered `torusLocalTheoryAPI`).
- **`mixedDensity`:** T18 `PeriodicInsertionAPI.forceDifference_mixed_bound`
  (`≤ C(ε^{α}+ε^{α+1})`) + `mixedRegionArithmetic` (`α>0`, `α+1>0`) driving both
  terms to `0` along `𝓝[>]0`; already-singular branch as above with
  `mixedLebesgueENormT q p 0 = 0`.
- **`energyTimeEmbedding`:** pure Mathlib (`lintegral ≤ essSup · measure` on
  `Ioo 0 T`, then `rpow ½`); no Section 3 node.
- **`closureInEnergy` / `simultaneousPairConvergence`:** T18 `energyRate` (`E_T`
  limit), `lifespan`, `solution`, `blowup`/`blowup_limsup` (`SpeedUnboundedAt` /
  `limsupLeft … speedENorm = ⊤` ⟹ `SingularTrajectoryT`), `force_mem`,
  `forceDifference_sobolev_bound`/`_negativeSobolev_tendsto` (simultaneous
  `L¹_tH^s`); `energyENormT T (u ε) ≠ ⊤` from the reference's finite `E_T` +
  correction/packet finiteness (`:554`).
- **`referenceFiniteEnergy`:** continuity of `reference.velocity` on the compact
  `[0,T]×T³` ⟹ finite `energyEssSupT`/`energyGradientT`.
- **`prop:projection` (all three fields):** `PeriodicDensityAPI.fixedInitialDensity`
  applied at each `a` (the paper derives `prop:projection` from `prop:density`);
  `0 ∈ initialClassT` for `zeroInitialProjection`; the `⊆` half of both image
  equalities by definitional membership in `extendedBreakdownSetT`.
- **T20 not consumed** (feeds `cor:nondensity` = T21).

## Open questions for the owner (the five of `RECONCILIATION.md` §4)

1. **Registration gap.** T18 (`PeriodicInsertionAPI`) + its T13/T15/T16/T17 chain
   are consumed by T19 but live only in `research/T18/Spec.lean`.  T19 restates
   `thm:insertion`'s conclusions in registered torus vocabulary (it cannot
   produce the T18 record the way R46 produces the registered `InsertionFamilyAPI`).
   Decide whether to **register the T18 torus insertion API before T19 assembly**;
   if registered, the T19 proof consumes it as a registered fact (mirroring R46).
   Direct analogue of T18's own open question about registering the T15 scaling
   chain.
2. **Sort.** `Prop` for all four (data-free, T24 precedent) vs the R41/R46
   registry convention of `Type`.  Confirm `Prop`, or align with the registered
   Section 4 twins as `Type`.
3. **`𝓧` topology.** `prop:projection`'s `:586` non-density remark (`{0}` not
   dense in a nontrivial normed `𝓧`) is not formalized — the paper keeps the
   `𝓧` topology generic and no registered `𝓧` topology exists.  Confirm the
   omission, or add a normed-`𝓧` carrier (a new statement, owner's call).
4. **`rem:peaks` (`:591`).** The concentration/force-amplitude remark
   (`‖g_ε−g‖_{L^∞}→∞`) sits in the projection subsection but is not one of T19's
   four results.  Confirm it is out of scope for the T19 contracts (or assign it
   as a separate remark-node).
5. **`regionExamples` spelling.** Confirm re-stating the `:538` illustration
   through the registered exponent at `ℝ≥0∞` points (`0 < alpha 2 1 ∧
   0 < alpha (4/3) 2`) rather than as disconnected real literals.
