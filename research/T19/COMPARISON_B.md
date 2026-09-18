# T19 draft B — paper-clause → Lean-field comparison (`prop:density`, `cor:mixed`, `cor:closure`, `prop:projection`)

Double-blind draft B, lane 372. Statement-only. File: `research/T19/DraftB.lean`
(elaborates, 0 errors). Namespace `BlowupDensity.T19.DraftB`. All four
structures are `Prop`-valued (no result introduces a constant/datum; approximant
forces and families are bound existentially inside fields).

Registered Section 4 twins used for the mirror: `MainThresholdsAPI` (R41,
`Contracts/V1/MainThresholds.lean`) and `CompletedDensityAPI` (R46,
`Contracts/V1/CompletedDensity.lean`).

## 1. `prop:density` — `PeriodicDensityAPI` (3 fields)

| paper clause (`03-torus.tex`) | Lean field | Section 4 counterpart |
|---|---|---|
| `:350-357` `∀g∀ρ∃f: ‖f-g‖_{L¹_tH^s}<ρ ∧ T_max^ν(a,f)≤T`, `s<1/2` | `fixedInitialDensity : … RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)` | `MainThresholdsAPI.fixedInitialDensity` (restricted to `q=1`) |
| `:355` threshold `1/2` | `thresholdValue : criticalOrder 1 = 1/2` | `MainThresholdsAPI.thresholdValues` (only the `q=1` half) |
| `:358-361` + `:626-631` regular-reference case: exact-`T` singularity via insertion | `regularReferenceSingular : … maximalLifespanT ν a f = ofReal T` | new split (Section 4 folds it into `regularReferenceApproximation`) |

Choices: density is stated through registered `RelativelyDenseT`/`breakdownSetT`
(`forceSobolevENormT` L¹, `q=1`). The torus `prop:density` covers only the
`L¹_tH^s` norm (the other norms are `cor:mixed`), so the field is `q=1` only,
unlike Section 4's `q∈{1,2}`. `regularReferenceSingular` records the sharper
`=ofReal T` that insertion gives on the regular case, versus the `≤ofReal T` of
the density set — the paper's own distinction (`:626-631`, "breakdown by `T`"
vs "singularity exactly at `T`").

## 2. `cor:mixed` — `MixedRegionAPI` (3 fields)

| paper clause | Lean field | counterpart |
|---|---|---|
| `:530-535` `eq:mixedregion` density for `3/p+2/q>3` | `mixedDensity : … RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)` | torus-only |
| `:534-535` proof: `α(p,q)>0`, hence `α+1>0` | `regionPositive : 3/p+2/q>3 → 0<αT p q ∧ 0<αT p q+1` | torus-only |
| `:536-538` region contains `L¹_tL²_x`, `L²_tL^{4/3}_x` | `regionExamples : (3/2+2/1>3) ∧ (3/(4/3)+2/2>3)` | torus-only |

Choices: `RelativelyDenseMixedT` is a local predicate — the exact mixed-norm
analogue of registered `RelativelyDenseT`, built from registered
`breakdownSetT`/`forceClassT` and the copied honest torus mixed norm
`mixedLebesgueENormT` (verbatim from `research/T18/Spec.lean:395-410`, itself
the T15 layer). The scaling exponent `alphaT` is copied from
`research/T18/Spec.lean:441-442` and drift-checked `:= rfl` against the
registered `BlowupDensity.Contracts.V1.alpha` (`Contracts/V1/Correction.lean`),
so `regionPositive` names the same `α` the T18 rate bound uses.

## 3. `cor:closure` — `StrongClosureAPI` (2 fields)

| paper clause | Lean field | counterpart |
|---|---|---|
| `:542-562` `eq:closure` `E_T` closure + `:558-560` simultaneous `E_T×L¹_tH^s` limit (`s<1/2`) + `:550-551` `u_ε` finite `E_T` | `strongClosure` (one existential family: per-`ε` force∈𝓕, exact lifespan `=ofReal T`, `energyENormT T (u ε)<⊤`, a `ClassicalSolutionT` with `velocity=u ε`, history on `[0,T-2ε²]`; then the `energyENormT` limit; then `∀s<1/2` the `forceSobolevENormT 1 s` limit) | `CompletedDensityAPI.strongTrajectoryClosure` |
| `:550-551` reference lies in ambient energy space (finite `E_T`) | `referenceFiniteEnergy : energyENormT T reference.velocity < ⊤` | implicit in Section 4 |

Choices: I mirror `strongTrajectoryClosure` but (i) thread a torus
`ClassicalSolutionT ν a g (T+δ)` reference instead of `ClassicalSolutionR`;
(ii) use `energyENormT` / `forceSobolevENormT`; (iii) the simultaneous force
limit is the single inhomogeneous `L¹_tH^s` (`s<1/2`) family — the torus
`cor:closure` states `E_T × L¹(0,∞;H^s)`, not the summed
`L¹_tH^0+L²_tH^{-1}+L²_tḢ^{-1}` of whole-space `prop:Renergy`. The velocity of
the approximant is pinned to a real solution and `history` is added (from the
insertion construction; matches `MainThresholdsAPI.regularReferenceApproximation`).
The set-theoretic `R_{a,T} ⊆ closure^{E_T}(S_{a,T})` and the norm-equivalence
`‖z‖_{L²_tL²}≤T^{1/2}‖z‖_{L^∞_tL²}` (`:552-560`) are stated operationally /
deferred — see ambiguities.

## 4. `prop:projection` — `ProjectionAPI` (3 fields)

| paper clause | Lean field | counterpart |
|---|---|---|
| `:568-577` density of `𝔅_{ν,T}` in `𝓧×𝓕` (product topology), `s<1/2` | `productDensity : … ∃ f ∈ 𝓕, ‖f-g‖<r ∧ maximalLifespanT ν a f ≤ ofReal T` | reduces to `prop:density` on the 𝓕-fibre (`:573-575`) |
| `:571-577` projection onto `𝓧` is all of `𝓧` (`∀a∃f`) | `projectionOntoInitial : ∀a∈𝓧, ∃f∈𝓕, T_max≤T` | Section 4 has no product/projection field (torus-specific `prop:projection`) |
| `:572-573,619-622` `a=0` family projects to `{0}` | `zeroInitialFiber : 0∈initialClassT ∧ ∃f∈𝓕, T_max^ν(0,f)≤T` | torus-only |

Choices: `𝔅_{ν,T}` is a set of *pairs* `(a,f)∈𝓧×𝓕`; the pair set is not
registered, so its three properties are stated on the components. The `∀a∃f`
order (`:616-619`) is respected in every field: `∀a` precedes `∃f`. `product-
Density` keeps the same `a` in both coordinates (the `U`-coordinate of `U×V` is
satisfied by `a` itself, per `:573-574`), so it is density of the *pair* set,
not of `𝓕` alone. `zeroInitialFiber` certifies `{0}⊆𝓧` and a singular force
over `0`, so the projected singleton is inhabited.

## Design choices (global)

- **Prop vs Type.** All four are `: Prop`: no result carries data (constructed
  forces/families are existential inside fields). The registered R41/R46 twins
  are `Type` only by registry convention (their fields are also all `Prop`s);
  the brief asks for Prop when there is no data, which is the case here.
- **Registered vs copied.** Registered `RelativelyDenseT`, `breakdownSetT`,
  `forceClassT`, `initialClassT`, `maximalLifespanT`, `RegularThroughT`,
  `ClassicalSolutionT`, `energyENormT`, `forceSobolevENormT`, `criticalOrder`,
  `Contracts.V1.alpha` are imported/used by name. Only the unregistered
  mixed-Lebesgue vocabulary (`IsPeriodicLebesgueSlicePath`, `mixedLebesgueENormT`,
  `alphaT`) is copied verbatim, in namespace `BlowupDensity.T15.Draft`, with the
  `alphaT := Contracts.V1.alpha` drift check.
- **No junk-value traps.** All suprema/distances are `ℝ≥0∞`
  (`forceSobolevENormT`, `mixedLebesgueENormT`, `energyENormT`); no `sSup`, no
  `.toReal`. The mixed norm carries its honest `⨅`-over-slice-paths structure
  (a missing `L^p(T³)` representative reports `⊤`, not a spurious small value).
  `ν>0`, `T>0`, `δ>0`, `r>0` are hypotheses on every field.
- **No T20.** The density package is constructive (proofs consume `thm:insertion`
  = T18), so `prop:critical` / `CriticalRegularityTAPI` (T20) is **not** imported.

## Ambiguities / points for reconciliation

1. **`prop:density` = Prop-structure or single `RelativelyDenseT` clause?** I
   split into 3 fields (density + threshold + exact-`T` regular case). Draft A
   may keep a single `fixedInitialDensity` field mirroring R41. Reconcile the
   `regularReferenceSingular` split (it is genuine — the paper's `:626-631`
   distinction — but arguably belongs to `cor:closure`).
2. **`cor:closure` set-inclusion `eq:closure`.** `R_{a,T}`, `S_{a,T}` are sets of
   *trajectories*; the `E_T`-closure of a trajectory set is heavy to register. I
   state the operational content (existence of `E_T`-convergent approximants
   with exact-`T` singular forces) instead of the literal `⊆ closure^{E_T}`.
   Draft A may register the sets. Reconcile.
3. **`cor:closure` norm-equivalence `:552-560`** (`E_T ↔ L²_tH¹` via
   `‖z‖_{L²_tL²}≤T^{1/2}‖z‖_{L^∞_tL²}`) is not a field: it needs a plain
   `L²(0,T;L²)` norm not registered (`energyGradientT` is the gradient version).
   Stated as a proof-side analytic lemma (see "needs a lemma"), not a statement
   clause. Reconcile whether to add a field.
4. **`prop:projection` non-density remark `:619-622`** ("`{0}` is not dense: if
   `a≠0`, the ball of radius `‖a‖/2` about `a` excludes `0`") needs an abstract
   normed topology on `𝓧`, which the paper deliberately leaves generic ("any
   topology on 𝓧", "a nontrivial normed initial-velocity space"). Not
   formalized; captured operationally by `zeroInitialFiber` + the `∀a∃f` order.
5. **Mixed density predicate.** Whether to register `RelativelyDenseMixedT` or
   inline the `∀g∀r∃f` in `cor:mixed`. I define the predicate (mirrors
   `RelativelyDenseT`). Reconcile with draft A's spelling.
6. **Region form.** I use the literal `3/p.toReal+2/q.toReal>3` (`eq:mixedregion`)
   and the equivalence `= (α(p,q)>0)` as a separate `regionPositive` field.
   Draft A may state the region as `0<alpha p q`. Reconcile.

## "Needs a lemma" — fields the proofs will consume

- **`prop:density` / `fixedInitialDensity`, `regularReferenceSingular`:**
  T18 `PeriodicInsertionAPI.lifespan` (`=ofReal T`),
  `.forceDifference_sobolev_bound` (`0≤s<1/2`),
  `.forceDifference_negativeSobolev_tendsto` (`s<0`), `.force_mem`; the trivial
  case needs only `breakdownSetInT` unfolding. `RegularThroughT` (T11) supplies
  the reference solution on `[0,T+δ)` = the insertion input.
- **`cor:mixed` / `mixedDensity`:** T18 `.forceDifference_mixed_bound`
  (`≤C(ε^{α}+ε^{α+1})`), `.forceDifference_mixed_memLp`, and `regionPositive`
  (`α>0`, `α+1>0`) to drive both terms to `0` (`𝓝[>]0`).
- **`cor:closure` / `strongClosure`:** T18 `.energyRate` (`E_T` limit),
  `.forceDifference_sobolev_bound`/`_negativeSobolev_tendsto` (simultaneous
  `L¹_tH^s`), `.history`, `.lifespan`, `.blowup`, `.force_mem`, `.solution`;
  the norm-equivalence `:552-560` is a self-contained Bochner lemma (Cauchy-
  Schwarz in time). `referenceFiniteEnergy` needs compactness of `[0,T]×T³`.
- **`prop:projection` / all three fields:** `PeriodicDensityAPI.fixedInitialDensity`
  (the paper derives `prop:projection` from `prop:density`), plus the abstract
  `projection_eq_univ_of_dense_fibers` / `fixed_slice_projection` topology lemmas.

## Implementation candidates (existing local Lean, `formalization/NSFormalization/`)

`grep -nE "^(def|structure|theorem|lemma) …"` in the Paper1/Paper3 modules named
in the T19 row of `SECTION3_PLAN.md` (`PeriodicDense`, `PeriodicDensityDichotomy`,
`PeriodicDensityFiber`) and neighbours:

- `Paper1/PeriodicDense.lean:41` `def GaugeDense`, `:60` `zero_slice_GaugeDense`,
  `:72` `admissible_slice_GaugeDense` — `prop:density` core.
- `Paper1/PeriodicDensityDichotomy.lean:137` `zero_slice_density_from_rest`,
  `:153` `periodic_density_fixed_slice_of_unforced_local` — the two-case proof.
- `Paper1/PeriodicDensityFiber.lean` — the `prop:projection` fibre.
- `Paper1/Topology.lean:17` `dense_of_insertion`, `:28` `not_dense_of_regular_ball`,
  `:36` `dense_relation_of_dense_fibers`, `:45` `projection_eq_univ_of_dense_fibers`,
  `:54` `fixed_slice_projection`, `:77` `density_threshold` — abstract engines for
  `prop:projection` and the dichotomy.
- `Paper1/ManuscriptTopology.lean:161` `DenseAt`, `:176` `denseAt_iff_approximation`,
  `:193` `denseAt_singularSlice_iff_GaugeDense`, `:228` `zero_slice_dense`,
  `:235` `admissible_slice_dense`, `:201` `not_denseAt_of_regular_ball` — topology.
- `Paper1/CorrectionMixedNorms.lean:13` `def mixedNorm`, `:123`
  `physical_force_mixed_bound`, `:188` `physical_force_mixed_tendsto_zero`, `:202`
  `physical_force_mixed_memLp` — `cor:mixed` rate/region.
- `Paper1/PeriodicMain.lean:32` `not_GaugeDense_of_GaugeSeparated`, `:44`
  `zero_slice_GaugeDense_iff_subcritical`; `Paper1/PeriodicSingleModeDensity.lean:75`
  `singleMode_density_branch`, `:94` `singleMode_admissible_density_branch`.

These are candidates for the eventual T19 binding layer; none is used in this
statement-only draft (contracts may not import `formalization/`).
