# T19 draft A — comparison: paper clauses → Lean fields

Double-blind draft A (lane 367). Statement-only. File `research/T19/DraftA.lean`
elaborates with 0 errors/warnings under
`cd verification && lake env lean ../research/T19/DraftA.lean`.

Node T19 = the density package: `prop:density` (`03-torus.tex:349-382`),
`cor:mixed` (`:528-539`), `cor:closure` (`:540-563`), `prop:projection`
(`:564-631`). Four `Prop`-valued structures, one `def …Statement : Prop` each.

Registered vocabulary imported and used by name (no copy):
`ClassicalSolutionT`, `maximalLifespanT`, `RegularThroughT`, `breakdownSetT`,
`breakdownSetInT`, `RelativelyDenseT`, `forceSobolevENormT`, `forceClassT`,
`initialClassT`, `MemForceT`, `energyENormT`, `energyEssSupT` (all
`Contracts/V1/TorusLocalTheory.lean`); `torusLift`, `periodicTorusMeasure`,
`PeriodicTorus`, `PeriodicSobolev`, `IsPeriodicSpatial` (`.TorusData`);
`SpatialField`, `SpaceTimeField`, `forceTimeMeasure`, `criticalOrder`,
`Space` (`.Data` / `NavierStokes.ProblemStatement`);
`BlowupDensity.Contracts.V1.alpha` (`.Correction`);
`MaximalPartial.{limsupLeft,speedENorm}` (`.MaximalPartial`).

Unregistered vocabulary copied verbatim from `research/T18/Spec.lean:396-433`
(delimited block, provenance comment): `IsPeriodicLebesgueSlicePath`,
`mixedLebesgueENormT`, `MemMixedLebesgueT`, `MemForceSobolevT`. These four are
**not** registered (only the whole-space `Data.mixedLebesgueENorm` is), and
`cor:mixed` cannot be stated without a torus mixed norm.

**Not copied, and why:** T18's `PeriodicInsertionAPI` /
`periodicInsertionStatement` and the entire T13–T17 chain they carry. The four
T19 results are pure `∀∃` statements expressible entirely in the registered
torus vocabulary; the regular-reference fields name the *conclusions* of
`thm:insertion` directly, exactly as the registered Section 4 counterparts
`MainThresholdsAPI.regularReferenceApproximation` and
`CompletedDensityAPI.strongTrajectoryClosure` do (neither references the
Section 4 insertion record either). Copying the ≈1900-line T18 chain verbatim
would import machinery (localization kernels, packet energy, scaling, potential,
correction) that T19 never reasons about. T20 (`prop:critical`) is **not**
consumed: it feeds `cor:nondensity` = node T21.

`s_c = 1/2` (torus fixes `q=1`, `SECTION3_PLAN.md` §4). `1/2 = criticalOrder 1`
numerically (`MainThresholdsAPI.thresholdValues`), but the paper writes `s<1/2`,
so the fields do too.

---

## 1. `prop:density` → `PeriodicDensityAPI` (`Prop`-valued; 3 fields)

| Paper clause (`03-torus.tex`) | Lean field | Section 4 counterpart |
|---|---|---|
| Statement `:351-357`, `∀g∀ρ∃f: ‖f-g‖_{L¹H^s}<ρ ∧ T_max≤T`, `a∈X`, `ν>0`, `T>0`, `s<1/2` | `density` = `RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)` | `MainThresholdsAPI.fixedInitialDensity` (`BreakdownDenseR`, `q∈{1,2}`, `s<s_q`) |
| Proof `:360` dichotomy on `T_max` | (not a field: `le_or_lt` is trivial; the two case-fields together are exhaustive) | — |
| Proof `:361-363` case `T_max≤T`, `f=g`, "already belongs to `B`", "norm difference is zero" | `alreadySingularApprox` (`∃f∈breakdownSetT`, `forceSobolevENormT 1 s (f−g)<r`; witness `f=g`) | (folded into R41 proof; not a separate registered field) |
| Proof `:364-368` case `T_max>T`: choose `δ`, insertion supplies `g_ε∈B` lifespan exactly `T`; `eq:Hsclose→0` for `0≤s<1/2`; `s=0`+`L²↪H^s` for `s<0` | `regularReferenceApprox` (`∃ε₀>0 ∃f`, per-`ε`: `f ε∈F`, `f ε−g∈F`, `maximalLifespanT=ofReal T`, `Nonempty ClassicalSolutionT`; nonneg-`s` limit; negative-`s` limit) | `MainThresholdsAPI.regularReferenceApproximation` |
| Remark `:625-631` breakdown *by* `T` (`≤`) not *exactly* `T`; density around earlier-breaking references only ≤ | documented: `density` uses `≤` (via `breakdownSetT`); `regularReferenceApprox` produces `= ofReal T` | (same distinction in R41) |

`def periodicDensityStatement` = the `density` field, paper order `a,ν,T,s`.

## 2. `cor:mixed` → `MixedRegionAPI` (`Prop`-valued; 4 fields)

| Paper clause | Lean field | Section 4 counterpart |
|---|---|---|
| Proof `:536-537` `α(p,q)>0` hence `α+1>0` on region | `mixedRegionArithmetic` (`3<3/p.toReal+2/q.toReal → 0<alpha p q ∧ 0<alpha p q+1`) | `MainThresholdsAPI.thresholdValues` / `R41.threshold_arithmetic` (analogue) |
| Statement `:530-534` density in `L^q_tL^p_x`, `1≤p,q≤∞`, `3/p+2/q>3` | `mixedDensity` (`∃f∈breakdownSetT`, `mixedLebesgueENormT q p (f−g)<r`) | torus-only (Section 4 `cor:Rclasses` is the closest analogue; different classes) |
| Proof `:535` case `T_max≤T`, `f=g` | `alreadySingularMixedApprox` | — |
| Proof `:535-538` case `T_max>T` `eq:Fclose→0` | `regularReferenceMixedApprox` (`∃ε₀ ∃f`; per-`ε` `f ε∈F`, exact lifespan; per-`(p,q)` in region: `MemMixedLebesgueT` honesty + `Tendsto mixedLebesgueENormT→0`) | `MainThresholdsAPI.regularReferenceApproximation` (Sobolev norm; here mixed) |

`def mixedRegionStatement` = the `mixedDensity` field, paper order.

Region encoding: `[Fact (1 ≤ p)]` gives `1≤p`, `1≤q` explicit, `p,q≤∞`
automatic in `ℝ≥0∞`. `3<3/p.toReal+2/q.toReal` uses `ENNReal.toReal ⊤ = 0`
consistently with the registered `alpha` (checked against T18's `alphaT`
comment). Endpoints `p=∞` or `q=∞` are therefore included exactly as `:531`.

## 3. `cor:closure` → `StrongClosureAPI` (`Prop`-valued; 3 fields)

| Paper clause | Lean field | Section 4 counterpart |
|---|---|---|
| Proof `:555-560` `‖z‖_{L²(0,T;L²)}≤T^{1/2}‖z‖_{L∞(0,T;L²)}`, the `E_T`↔`L²_tH¹` equivalence | `energyTimeEmbedding` (`spaceTimeL2L2ENormT T z ≤ ofReal(√T)·energyEssSupT T z`) | torus-only (Section 4 uses the whole-space `energyENorm` directly) |
| Statement `:546-547` `eq:closure` `R_{a,T}⊆closure(S_{a,T})^{E_T}` | `closureInEnergy` (∀ `u∈R`, ∀`r>0`, ∃`u'∈S`, `energyENormT T (u−u')<r`; `R`/`S` = `RegularTrajectoryT`/`SingularTrajectoryT`) | torus-only |
| Statement `:548-552` pairs `(u_ε,g_ε)→(v,g)` in `E_T×L¹_tH^s`, `s<1/2` | `simultaneousPairConvergence` (reference `ClassicalSolutionT ν a g (T+δ)`; `∃ε₀ ∃u f`; per-`ε` `f ε∈F`, exact lifespan, `∃` solution with velocity `u ε`, `SingularTrajectoryT`; `E_T` limit; `∀s<1/2` `L¹H^s` limit) | `CompletedDensityAPI.strongTrajectoryClosure` (energy + three force norms; here energy + single Sobolev) |

`def strongClosureStatement` = the `closureInEnergy` field (`eq:closure`).

`RegularTrajectoryT`/`SingularTrajectoryT` render the paper's sets `R`/`S` over
registered classical solutions; "unbounded max velocity at `T`" =
`MaximalPartial.limsupLeft T (t↦speedENorm(u(t,·)))=⊤`. "finite `E_T`" =
`energyENormT T u ≠ ⊤`. "smooth on `[0,T)`" = a `ClassicalSolutionT` on horizon
`T` (smooth on `Ico 0 T`).

## 4. `prop:projection` → `ProjectionAPI` (`Prop`-valued; 3 fields)

| Paper clause | Lean field | Section 4 counterpart |
|---|---|---|
| Statement `:568-570` density of `𝔅_{ν,T}` in product topology, `s<1/2` | `extendedProductDensity` (initial datum kept at `a`; `∃f`, `(a,f)∈extendedBreakdownSetT`, `forceSobolevENormT 1 s (f−g)<r`) | torus-only (no Section 4 product-topology statement) |
| Statement `:570`, `:577-578`, remark `:582-585` `∀a∃f`, projection onto `X` is all of `X` | `projectionOntoInitialData` (`Prod.fst '' extendedBreakdownSetT ν T = initialClassT`) | torus-only |
| Statement `:571-572`, `:579` `a=0` subfamily projects to `{0}` | `zeroInitialProjection` (`Prod.fst '' {p∈𝔅 ∣ p.1=0} = {0}`) | torus-only |

`def projectionStatement` = product-density (force factor) ∧ full projection,
paper order `ν,T`. `𝔅_{ν,T}` = `extendedBreakdownSetT ν T ⊆ 𝓧×𝓕`.

---

## Choices

- **Prop vs Type.** All four are `Prop`. Each result is a pure `∀∃` claim; the
  only constants/data (`M,D,C_{p,q},C_s,c`) live inside T18/T20, not T19. So no
  `Type`-valued fields (contrast T18's `PeriodicInsertionAPI`, which carries the
  family and thresholds as data and is `Type`-valued).
- **Density as ε-approximation, not topological closure.** `density`,
  `closureInEnergy`, `extendedProductDensity` render "dense"/"closure" as
  positive-radius approximation (∀`r>0` ∃ witness with distance `< r`), exactly
  as the registered `RelativelyDenseT`/`RelativelyDense`. This avoids needing a
  `TopologicalSpace`/pseudometric instance on force space and is the repository's
  established convention (`Data.RelativelyDense` docstring).
- **Regular-reference conclusions spelled in registered vocab**, mirroring
  `MainThresholdsAPI.regularReferenceApproximation` / `strongTrajectoryClosure`,
  rather than existentially producing a `PeriodicInsertionAPI` (unregistered,
  huge). Same faithful content, self-contained file.
- **One inserted family per case, valid across all `s`/`(p,q)`.** The inserted
  `g_ε` is `s`-independent; the `∀s` (resp. `∀(p,q)`) quantifier sits *inside*
  the family existential, faithful to the proof (choose `g_ε`, then read off
  `eq:Hsclose`/`eq:Fclose` for each exponent).
- **Honesty guards.** Every totalized `⨅`-norm limit carries its Bochner-path
  guard (`MemForceSobolevT`, `MemMixedLebesgueT`) so the `Tendsto→0` is not
  vacuously about `⊤`; strict `< r` bounds are self-guarding (a `⊤` distance
  fails `< r`).
- **`s<1/2` written literally** (not `criticalOrder 1`), matching `:351`; the
  numeric identity is noted in the module docstring.
- **Breakdown *by* vs *exactly* `T`.** `density`/`extendedProductDensity` use
  `≤ ofReal T` (`breakdownSetT`/`extendedBreakdownSetT`); the regular-reference
  fields assert `= ofReal T`. This is the `:625-631` distinction.

## Ambiguities / judgment calls (flag for reconciliation with draft B)

1. **Field granularity of `prop:density`.** The paper statement is one line; I
   split into `density` + two case fields (`alreadySingular*`, `regularReference*`)
   to render the proof. An alternative is a single `density` field with the cases
   as a separate `dichotomy` lemma. I judged the case fields to be genuine
   proof clauses (`:361-368`), not padding.
2. **"any topology on `X`" in `prop:projection`.** I render product density by
   *keeping the initial datum fixed at `a`* (its own point lies in every
   `X`-neighborhood, so the `X`-factor is discharged topology-independently). An
   alternative would parametrize an abstract `TopologicalSpace 𝓧` and quantify
   over neighborhoods; I chose the fixed-`a` form as it is topology-agnostic and
   matches the proof `:573-576` ("The initial datum `a` already belongs to `U`").
3. **`zeroInitialProjection` as an image equality `= {0}`.** The `⊆` direction
   is the `a=0` constraint (trivial); the content is `⊇` (nonemptiness = a real
   singular force over `0`). Rendering as `Prod.fst '' {…} = {0}` keeps it a
   single non-vacuous set equality rather than a bare tautology.
4. **`energyTimeEmbedding` constant.** Rendered as `ofReal (Real.sqrt T)`
   (`T^{1/2}`). The paper's `‖z‖_{L²(0,T;L²)}≤T^{1/2}‖z‖_{L∞(0,T;L²)}` is the
   single displayed inequality of `:555-556`; the fuller two-sided equivalence
   (`:557-560`) is described in the docstring, not split into a second field.
5. **`cor:closure` reference as `ClassicalSolutionT ν a g (T+δ)`.** "smooth
   through `T`" is `RegularThroughT`; I thread the reference solution and take
   `v = reference.velocity`, exactly as `strongTrajectoryClosure` threads its
   `R : ClassicalSolutionR ν a g (T+δ)`.

## "Needs a lemma" — T11 / T12 / T18 fields the eventual proof will consume

- **`density.regularReferenceApprox` / all `regularReference*` fields:**
  T18 `periodicInsertionStatement` (i.e. `PeriodicInsertionAPI`) fields
  `force_mem`, `forceDifference_mem`, `lifespan` (`= ofReal T`), `solution`,
  `forceDifference_sobolev_bound` + `forceDiffSobolevConst_pos`
  (⟹ `0≤s<1/2` `Tendsto`), `forceDifference_negativeSobolev_tendsto`
  (⟹ `s<0` `Tendsto`), `forceDifference_mixed_bound` +
  `forceDiffMixedConst_nonneg` + `mixedRegionArithmetic` (⟹ mixed `Tendsto`),
  `energyRate` (⟹ `E_T` `Tendsto`), `forceDifference_mixed_memLp`,
  `forceDifference_sobolev_memLp`, `negative_s_memLp` (honesty guards).
- **The T18 hypotheses** need a producer of `PacketImportAPI`/`PlacementData`/
  `ScalingAPI`/`CutoffData`/`CorrectionAPI` and a reference
  `ClassicalSolutionT ν a g (T+δ)`; the reference comes from `ofReal T <
  maximalLifespanT ν a g` unfolded through `maximalLifespanT`'s definition
  (a solution on some horizon `> T`).
- **Dichotomy (`density`):** `le_or_lt (maximalLifespanT ν a g) (ofReal T)`
  (Mathlib), then case 1 uses `forceSobolevENormT` of the zero field `= 0`
  (`eLpNorm`/`⨅` of `0`), case 2 the T18 bundle above.
- **`alreadySingular*`:** `breakdownSetInT` membership from the hypotheses;
  `forceSobolevENormT 1 s 0 = 0` (norm of zero field) `< r`.
- **`cor:closure.energyTimeEmbedding`:** Hölder/`eLpNorm` monotonicity in time
  on `Ioo 0 T` (Mathlib `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` style), no
  Section 3 node.
- **`cor:closure.closureInEnergy` / `simultaneousPairConvergence`:** T18
  `energyRate` (⟹ `E_T` convergence) + `lifespan` + `solution` + `blowup`
  (`SpeedUnboundedAt`/`blowup_limsup` ⟹ `SingularTrajectoryT`'s
  `limsupLeft…=⊤`), plus `energyENormT (u_ε) ≠ ⊤` from the reference's finite
  `E_T` and the correction/packet finiteness (`:553`).
- **`prop:projection` (all fields):** `prop:density` itself (i.e.
  `PeriodicDensityAPI.density`), applied at each `a`, plus `0 ∈ initialClassT`
  (smoothness/periodicity/solenoidality of the zero field) for
  `zeroInitialProjection`.
- **T11 (`prop:local`):** consumed transitively through T18's lifespan/
  uniqueness argument (`PeriodicLocalTheoryAPI.velocity_unique`,
  `exists_maximal`, `maximal_unique`; `PeriodicContinuationH3API.extendsBeyond`).
  T19 does not consume T11 directly at the field level.
- **T12 / T20:** not consumed by T19 (T12 feeds T18/T20; T20 feeds T21).

## Implementation candidates (`formalization/NSFormalization/Paper1/`)

These local Paper1 modules already carry the density argument in a *different*
(pre-contract) vocabulary — `TestForce`, `IsTestForce`, gauge norms — and are
the binding targets, not the spec vocabulary:

- `Paper1/PeriodicDense.lean`: `singularSlice`, `GaugeApprox`, `GaugeDense`
  (defs); `zero_slice_GaugeDense`, `admissible_slice_GaugeDense` (theorems). —
  candidate for `PeriodicDensityAPI.density`.
- `Paper1/PeriodicDensityFiber.lean`: `forceDistance`, `MaximalFlowIdentified`
  (defs); `exists_periodic_singular_force_approximation`,
  `exists_periodic_insertion_fiber_member`,
  `exists_periodic_singular_total_force_approximation(_identified)` (theorems).
  — candidate for the `regularReferenceApprox` fiber.
- `Paper1/PeriodicDensityDichotomy.lean`: `flowWithForce`, `restingFlow`,
  `UnforcedLocalExistence` (defs); `exists_nearby_singular_force_of_localFlow`,
  `…_of_unforced_localFlow`, `…_from_rest`, `zero_slice_density_from_rest`,
  `periodic_density_fixed_slice_of_unforced_local` (theorems). — candidate for
  the two-case dichotomy (`alreadySingularApprox` / `regularReferenceApprox`).

None of these are in the registered contract vocabulary, so the T19 binding
layer will need fieldwise conversions (as in the T11 structure exception), not
`rfl` bridges. The T19 *spec* here is written purely in the registered
`ClassicalSolutionT`/`maximalLifespanT`/`forceClassT`/… vocabulary.
