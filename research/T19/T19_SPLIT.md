# T19 — proof-lane split (the density package on `T³`: `prop:density` `03-torus.tex:349-382`, `cor:mixed` `:528-539`, `cor:closure` `:540-563`, `prop:projection` `:564-631`)

Lead-facing, 2026-09-18. Target = the four reconciled structures of `research/T19/Spec.lean`
(namespace `BlowupDensity.T19`): **`PeriodicDensityAPI` 3 / `MixedRegionAPI` 3 / `StrongClosureAPI` 4 /
`ProjectionAPI` 3 = 13 fields**, plus the four `…Statement : Prop` (`periodicDensityStatement:251`,
`mixedRegionStatement:323`, `strongClosureStatement:438`, `projectionStatement:518`). Design =
`research/T19/RECONCILIATION.md` §2-§4 + `COMPARISON.md` "Proof dependencies". Twins (same proof skeleton) =
Section 4 R41 `MainThresholdsAPI` (`Contracts/V1/MainThresholds.lean`, `Bindings/MainThresholds.lean`,
`Bindings/DensityFromInsertion.lean`, `Section4/R41/*`) and R46 `CompletedDensityAPI`
(`Contracts/V1/CompletedDensity.lean`, `Bindings/CompletedClosure.lean`). House style =
`research/T11/T11_SPLIT.md`, `research/T18/T18_SPLIT.md`.
Size: **S** ≤ ~100 lines; **M** one self-contained lemma with a known proof; **L** a multi-file campaign.
Model: `codex-sol` = reuse/transport/algebra/bookkeeping; `Opus` = analytic core.

## 0. Ground rules

**Peeling rule (T11/T18).** Every unit ends in a `theorem` whose statement **is** a T19 `Spec.lean` field
verbatim, or a lemma directly consumed by one. A unit that cannot close from the tree names **exactly one**
input hypothesis (written out, non-tautological, discharged by a later unit); **no** named input for the
hard analytic units.

**T19 consumes `thm:insertion` (T18) as a black box — the one named input of every constructive field.**
Exactly as R41/R46 restate insertion conclusions rather than reason inside the insertion record, and
because a registered `Contracts/V1` file may import only `Contracts.*` while `PeriodicInsertionAPI` lives in
the unregistered `research/T18/Spec.lean`, the T19 *contract* only names insertion's conclusions in
registered torus vocabulary; the T19 **proof** consumes T18 as a **registered fact**. So every field that
inserts a nearby singular force (`fixedInitialDensity`, `regularReferenceSingular`, `mixedDensity`,
`simultaneousPairConvergence`, and — transitively — the projection fields and `closureInEnergy`) is
**blocked on T18 U12** (the T18 assembly/registration + `periodicInsertionStatement`, `research/T18/Spec.lean:1977`;
`research/T18/T18_SPLIT.md` §1 U12). Its named input is the registered T18 insertion API, consumed via a
torus `insertionFromData`-style constructor mirroring `Bindings/InsertionFromData.lean` /
`insertionLifespanV2_of_data`. The field *theorem* is otherwise a pure recombination of T18 outputs.

**The `prop:density` dichotomy — how "already singular by `T`" vs "regular through `T`" is discharged.**
The pivot is `maximalLifespanT ν a g` against `ENNReal.ofReal T`; the discharge is the exact torus copy of
`Bindings/DensityFromInsertion.lean:breakdownDenseR_of_subcritical`:
- `by_cases hLife : maximalLifespanT ν a g ≤ ENNReal.ofReal T` (Mathlib `le_or_lt`).
- **Already-singular branch** (`≤ ofReal T`): `g` is itself in `breakdownSetT ν a T`; take `f = g`, distance
  `forceSobolevENormT 1 s 0 = 0 < r` (U6). **No T18, no T11.**
- **Regular branch** (`¬ ≤`, i.e. `maximalLifespanT ν a g > ofReal T`): feed T18's insertion. The paper's
  "regular through `T`" hypothesis is the registered `RegularThroughT ν a g T := ∃ δ>0, Nonempty
  (ClassicalSolutionT ν a g (T+δ))` (`Contracts/V1/TorusLocalTheory.lean:205`), which
  `MaximalPartial.regularThrough_iff` (`Contracts/V1/MaximalPartial.lean:200`) turns into
  `maximalLifespanT ν a g > ofReal T` and back — exactly the R41 binding step
  `Bindings/MainThresholds.lean:98` `(maximalPartial.regularThrough_iff …).mp`. T18 then yields `f = force ε`
  with `maximalLifespanT ν a (force ε) = ofReal T` (**exactly**), so `≤ ofReal T` (in the breakdown set) for
  the density field, and `= ofReal T` for the sharp `regularReferenceSingular`.
- **T11 uniqueness (`PeriodicLocalTheoryAPI.velocity_unique`, `Contracts/V1/TorusLocalTheory.lean:467`)** enters
  only the *regular-reference / closure* fields, to identify T18's internal reference velocity with the
  velocity of the given `ClassicalSolutionT ν a g (T+δ)` on `[0,T)` — the R41 binding step
  `Bindings/MainThresholds.lean:104-116` (`href`, via `uniqueness.velocity_unique`) — so the `E_T` energy
  limit and the `RegularTrajectoryT` identification line up.

**No honesty guards, no `TopologicalSpace` on force/trajectory space.** Every closeness is strict `< r` or
`Tendsto … (𝓝[>]0) (𝓝 0)`, self-guarding in `ℝ≥0∞` (R41/R46 carry none); density is ε-approximation
(`RelativelyDenseT`, `RelativelyDenseMixedT`, `closureInEnergy`).

**Candidate reuse (`SECTION3_PLAN.md` T19 row).** The `Paper1/` sketches are proof scaffolds to mine, not
final targets (they are stated over `IsTestForce`/`GaugeDense`, not the registered `forceClassT`/
`RelativelyDenseT`): `PeriodicDensityDichotomy.lean:74 exists_nearby_singular_force_of_localFlow`,
`:127 exists_nearby_singular_force_from_rest`, `:153 periodic_density_fixed_slice_of_unforced_local` (the
dichotomy shape for U7/U8); `PeriodicDensityFiber.lean:83 exists_periodic_singular_force_approximation`,
`:116 exists_periodic_insertion_fiber_member` (the fibre/projection shape for U10-U12); `PeriodicDense.lean:60
zero_slice_GaugeDense`, `:72 admissible_slice_GaugeDense` (the `a=0` fibre for U12). Transcribe the skeleton;
re-target every conclusion to the registered vocabulary.

## 1. Units

`𝓑 := breakdownSetT ν a T`; `𝔅 := extendedBreakdownSetT ν T`; `R/S := RegularTrajectoryT/SingularTrajectoryT`;
`ins := ` the registered T18 `PeriodicInsertionAPI` obtained from `RegularThroughT ν a g T` (T18 U12).

### Wave 1 — pure arithmetic / bookkeeping, **unblocked today** (no T18)

- **U1 — `thresholdValue`.** Target (verbatim, `Spec.lean:221`): `criticalOrder 1 = (1:ℝ)/2`. Route: exactly
  R41 `Bindings/MainThresholds.lean:96` `thresholdValues := by norm_num [criticalOrder]` (`criticalOrder 1
  = 2/1 − 3/2 = 1/2`). **S, codex-sol.** No named input. Deps: —.

- **U2 — `mixedRegionArithmetic`.** Target (`Spec.lean:301`): `∀ p q, 3 < 3/p.toReal + 2/q.toReal →
  0 < alpha p q ∧ 0 < alpha p q + 1`. Route: unfold registered `Contracts.V1.alpha p q =
  −3 + 3/p.toReal + 2/q.toReal` (`Correction.lean:160`); first conjunct `linarith` from the hypothesis,
  second `linarith` from the first. **S, codex-sol.** No named input. Deps: —.

- **U3 — `regionExamples`.** Target (`Spec.lean:318`): `0 < alpha 2 1 ∧ 0 < alpha (4/3) 2`. Route: unfold
  `alpha`, reduce `(2:ℝ≥0∞).toReal`, `(1:ℝ≥0∞).toReal`, `((4/3):ℝ≥0∞).toReal`, `(2:ℝ≥0∞).toReal` (finite
  numerals, `ENNReal.toReal_ofNat`/`toReal_div`), `norm_num` (`α(2,1)=1/2`, `α(4/3,2)=1/4`). **S, codex-sol.**
  No named input. Deps: U2 (reuse the `alpha`-unfold lemma).

- **U4 — `energyTimeEmbedding`.** Target (`Spec.lean:352`): `spaceTimeL2L2ENormT T z ≤
  ENNReal.ofReal (Real.sqrt T) * energyEssSupT T z`. Route (pure Mathlib, hard analytic): with
  `h t := eLpNorm (torusLift (fun x => z (t,x))) 2 periodicTorusMeasure`,
  `spaceTimeL2L2ENormT T z = (∫⁻ t in Ioo 0 T, (h t)^2)^(1/2)`; `∫⁻_{Ioo 0 T} (h t)^2 ≤
  (essSup h (volume.restrict (Ioo 0 T)))^2 · volume (Ioo 0 T)` (`lintegral_le_essSup_mul` /
  `setLIntegral_const`-style), `volume (Ioo 0 T) = ofReal T` (`Real.volume_Ioo`), then `rpow (1/2)`
  monotone + `ENNReal.mul_rpow_of_nonneg` + `(ofReal T)^(1/2) = ofReal (Real.sqrt T)`
  (`ENNReal.ofReal_rpow`/`Real.sqrt_eq_rpow`), and `energyEssSupT T z = essSup h …` by unfolding
  `TorusLocalTheory.lean`. `RECONCILIATION.md` "False clauses" #1 verifies the identity. **M, codex-sol**
  (Opus if the `essSup·measure` + `rpow` bookkeeping stalls). **No named input.** Deps: —.

- **U5 — `referenceFiniteEnergy`.** Target (`Spec.lean:428`): `∀ … ∀ reference : ClassicalSolutionT ν a g
  (T+δ), energyENormT T reference.velocity < ⊤`. Route: `reference.velocity` is smooth on
  `Ico 0 (T+δ) ×ˢ univ` (`ClassicalSolutionT.velocity_smooth`), and `[0,T]×T³` is compact with `T < T+δ`, so
  velocity and gradient are bounded there ⟹ `energyEssSupT T`, `energyGradientT T` finite ⟹ `energyENormT T
  reference.velocity < ⊤` (`energyENormT` is their `ℝ≥0∞` sum, `TorusLocalTheory.lean:246`). Mirror of the
  R46 implicit "reference finite `E_T`" step. **M, codex-sol.** No named input. Deps: —.

- **U6 — zero-difference norm helpers** (lemmas directly consumed by the already-singular branch). Targets:
  `torusForceSobolevENorm_zero : ∀ q s, forceSobolevENormT q s 0 = 0` (exact torus copy of
  `Bindings/DensityFromInsertion.lean:16 density_forceSobolevENorm_zero`) and `torusMixedLebesgueENormT_zero :
  ∀ q p, mixedLebesgueENormT q p 0 = 0` (mirror `I03.forceHomogeneousENorm_zero`, used in
  `Bindings/CompletedClosure.lean:186`). Route: the `⨅` over datum/slice paths is `≤` the zero representative,
  whose `eLpNorm`/`bochnerDatumENorm` is `0`. **S, codex-sol.** No named input. Deps: —.

### Wave 2 — the density engine + its two siblings, **blocked on T18 U12** (Opus)

- **U7 — `fixedInitialDensity` (the dichotomy engine).** Target (verbatim, `Spec.lean:207`): `∀ a∈𝓧, ∀ ν>0,
  ∀ T>0, ∀ s<1/2, RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)`. Route: exact torus copy of
  `breakdownDenseR_of_subcritical` (`Bindings/DensityFromInsertion.lean:24-51`). `intro … g hg r hr`;
  `by_cases hLife : maximalLifespanT ν a g ≤ ofReal T`; **already-singular** → `⟨g, ⟨hg, hLife⟩, by simpa
  [sub_self, U6] using hr⟩`; **regular** → `hlong := lt_of_not_ge hLife`, build `ins` from T18 U12
  (`RegularThroughT`⇐`hlong` via `regularThrough_iff`), take the eventual-`< r` from `ins.forceDifference_sobolev_bound`
  (`0≤s<1/2`, `research/T18/Spec.lean:1948`) / `ins.forceDifference_negativeSobolev_tendsto` (`s<0`, `:1957`)
  driving `ofReal T`-scaled powers to `0` along `𝓝[>]0`, pick `ε ∈ Ioc 0 ins.ε₀` (`Ioc_mem_nhdsGT`), witness
  `⟨ins.force ε, ⟨ins.force_mem ε …, (ins.lifespan ε … ).le⟩, hdist⟩` (`force_mem :1741`, `lifespan :1812`).
  **L, Opus.** **One named input: registered T18 `PeriodicInsertionAPI` (T18 U12).** Deps: U6. Blocked on T18 U12.

- **U8 — `regularReferenceSingular` (sharp, exactly-`T`).** Target (verbatim, `Spec.lean:240`): `… ∀ g∈𝓕,
  RegularThroughT ν a g T → ∀ s<1/2, ∀ r>0, ∃ f∈𝓕, forceSobolevENormT 1 s (f−g) < r ∧ maximalLifespanT ν a f
  = ofReal T`. Route: no `by_cases` — the hypothesis **is** the regular branch. From `RegularThroughT ν a g
  T` build `ins` (T18 U12); the eventual-`< r` as in U7; witness `ins.force ε` with the **exact** equality
  `ins.lifespan ε … : maximalLifespanT ν a (ins.force ε) = ofReal T` (`:1812`, not `.le`). Mirrors the sharp
  half of R41 `regularReferenceApproximation` (`Bindings/MainThresholds.lean:97-136`). **M-L, Opus.** One
  named input: T18 `PeriodicInsertionAPI` (T18 U12). Deps: U7 (shared eventual-`< r` helper). Blocked on T18 U12.

- **U9 — `mixedDensity`.** Target (verbatim, `Spec.lean:281`): `∀ a∈𝓧, ∀ ν>0, ∀ T>0, ∀ (p q)[Fact(1≤p)],
  1≤q → 3 < 3/p.toReal+2/q.toReal → RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)`. Route:
  same dichotomy as U7 in the copied torus mixed norm `mixedLebesgueENormT q p` — already-singular via U6
  (`mixedLebesgueENormT q p 0 = 0`); regular via `ins.forceDifference_mixed_bound` (`:1919`,
  `≤ C(ε^α + ε^{α+1})`) with U2's `0 < alpha p q ∧ 0 < alpha p q + 1` driving both powers to `0` along
  `𝓝[>]0` (mirror `Bindings/CompletedClosure.lean:closure_relativeHomogeneous` at `:180`). **M-L, Opus.**
  One named input: T18 `PeriodicInsertionAPI` (T18 U12). Deps: U2, U6. Blocked on T18 U12.

### Wave 3 — the closure family, **blocked on T18 U12** (Opus + codex)

- **U13 — `simultaneousPairConvergence`.** Target (verbatim, `Spec.lean:395`): for a reference
  `ClassicalSolutionT ν a g (T+δ)`, one family `(u,f)` with per-`ε` `f ε∈𝓕 ∧ maximalLifespanT ν a (f ε) =
  ofReal T ∧ (∃ w:ClassicalSolutionT ν a (f ε) T, w.velocity = u ε) ∧ SingularTrajectoryT ν a T (u ε)`, plus
  `energyENormT`-limit of `u ε − reference.velocity` and the `∀ s<1/2` `forceSobolevENormT 1 s`-limit, both
  along `𝓝[>]0`. Route: exact torus copy of `Bindings/CompletedClosure.lean:122
  strongTrajectoryClosure_of_realization` (restated over registered conclusions, no `InsertionFamilyAPI`
  export). `RegularThroughT ν a g T` ⇐ `⟨δ, hδ, ⟨reference⟩⟩` builds `ins` (T18 U12); per-`ε`: `f ε :=
  ins.force ε` (`force_mem :1741`, `lifespan = ofReal T :1812`, `solution :1796` gives `w`);
  `SingularTrajectoryT (u ε)` from finite `E_T` (U5 + `ins.energyRate :1892` triangle) and blow-up
  (`ins.blowup_limsup :1825` ⟹ `limsupLeft T (speedENorm∘u ε) = ⊤`); `E_T` limit via `ins.energyRate` after
  identifying `reference.velocity` with `ins`'s internal `v` on `[0,T)` by T11 `velocity_unique` (the R41
  `href` step, `Bindings/MainThresholds.lean:104-124`); `L^1_tH^s` limit as in U7
  (`forceDifference_sobolev_bound`/`_negativeSobolev_tendsto`). **L, Opus.** One named input: T18
  `PeriodicInsertionAPI` (T18 U12). Deps: U5, U7 (shared helpers). Blocked on T18 U12.

- **U14 — `closureInEnergy` (`eq:closure` set inclusion, ε-form).** Target (verbatim, `Spec.lean:370`):
  `∀ a∈𝓧, ∀ ν>0, ∀ T>0, ∀ u, RegularTrajectoryT ν a T u → ∀ r>0, ∃ u', SingularTrajectoryT ν a T u' ∧
  energyENormT T (u − u') < r`. Route: `RegularTrajectoryT` (`Spec.lean:138`) unpacks to `g∈𝓕`, `δ>0`,
  `w:ClassicalSolutionT ν a g (T+δ)` with `w.velocity = u`; feed U13 at that reference to get the `(u,f)`
  family; from the `energyENormT`-`Tendsto` extract `ε` with `energyENormT T (u ε − reference.velocity) < r`
  (`reference.velocity = u`), set `u' := u ε` (a `SingularTrajectoryT` by U13's per-`ε` clause). **M,
  codex-sol** (Opus if the filter-`.exists` bookkeeping stalls). No new named input (consumes U13). Deps: U13.
  Blocked (via U13/T18 U12).

### Wave 4 — projection, derived from density, **blocked** (via U7; codex)

- **U10 — `extendedProductDensity`.** Target (verbatim, `Spec.lean:471`): `∀ ν>0, ∀ T>0, ∀ s<1/2, ∀ a∈𝓧,
  ∀ g∈𝓕, ∀ r>0, ∃ f, (a,f) ∈ extendedBreakdownSetT ν T ∧ forceSobolevENormT 1 s (f−g) < r`. Route: apply U7
  `fixedInitialDensity` at `(a,ν,T,s)`, unfold `RelativelyDenseT`/`breakdownSetT` on `g,r` to get `f` with
  `f∈𝓕 ∧ maximalLifespanT ν a f ≤ ofReal T ∧ ‖f−g‖<r`, repackage the first two as membership in
  `extendedBreakdownSetT ν T` (`Spec.lean:160`, definitional). **S-M, codex-sol.** No new named input
  (consumes U7). Deps: U7. Blocked (via U7).

- **U11 — `projectionOntoInitialData`.** Target (verbatim, `Spec.lean:492`): `∀ ν>0, ∀ T>0, Prod.fst ''
  (extendedBreakdownSetT ν T) = initialClassT`. Route: `Set.ext`; `⊆` by `rintro ⟨a,f⟩ ⟨ha,_,_⟩` (the
  `extendedBreakdownSetT` membership carries `a∈initialClassT`); `⊇` from U10/U7 — for `a∈𝓧` pick any
  `g∈forceClassT` (e.g. the zero force, `0∈forceClassT`) and any `r`, U10 gives `f` with `(a,f)∈𝔅`, so
  `a ∈ Prod.fst '' 𝔅`. **M, codex-sol.** No new named input. Deps: U7, U10. Blocked (via U7).

- **U12 — `zeroInitialProjection`.** Target (verbatim, `Spec.lean:508`): `∀ ν>0, ∀ T>0, Prod.fst ''
  {p | p ∈ extendedBreakdownSetT ν T ∧ p.1 = fun _ => 0} = {(fun _ => 0 : SpatialField)}`. Route: `Set.ext`;
  `⊆` from the constraint `p.1 = 0`; `⊇` needs the fibre over `0` nonempty — `0 ∈ initialClassT`
  (mirror `Section4/A04/ZeroSolution.lean:zero_mem_initialClassR`, used at
  `Bindings/DensityFromInsertion.lean:57`) + U10/U7 at `a=0` gives `f` with `((fun _=>0), f)∈𝔅`. **M,
  codex-sol.** One named input: `0 ∈ initialClassT` (a T10/T11 data fact; discharge by the torus
  `zero_mem_initialClassT` analogue). Deps: U7, U10. Blocked (via U7).

## 2. Proof-dependency ledger (which registered declaration each unit consumes; from RECONCILIATION §4)

| unit | field | T18 `PeriodicInsertionAPI` (via U12) | T11 (registered) | other | T18-gated |
|---|---|---|---|---|---|
| U1 | `thresholdValue` | — | — | `criticalOrder` (`Data.lean:259`) | no |
| U2 | `mixedRegionArithmetic` | — | — | `alpha` (`Correction.lean:160`) | no |
| U3 | `regionExamples` | — | — | `alpha` + `toReal` numerals | no |
| U4 | `energyTimeEmbedding` | — | — | Mathlib `lintegral`/`essSup`/`rpow`; `energyEssSupT` | no |
| U5 | `referenceFiniteEnergy` | — | `ClassicalSolutionT.velocity_smooth` | compactness of `[0,T]×T³`; `energyENormT` | no |
| U6 | zero-norm helpers | — | — | `forceSobolevENormT`/`mixedLebesgueENormT` `iInf` | no |
| U7 | `fixedInitialDensity` | `lifespan`, `force_mem`, `forceDifference_sobolev_bound`, `forceDifference_negativeSobolev_tendsto` | `RegularThroughT` + `regularThrough_iff` | `maximalLifespanT`; U6 | **yes** |
| U8 | `regularReferenceSingular` | `lifespan (= ofReal T)`, `force_mem`, `forceDifference_sobolev_bound/_negativeSobolev_tendsto` | `RegularThroughT`, `regularThrough_iff` | U7 helper | **yes** |
| U9 | `mixedDensity` | `forceDifference_mixed_bound` | `RegularThroughT` | U2, U6; `mixedLebesgueENormT` | **yes** |
| U13 | `simultaneousPairConvergence` | `force_mem`, `lifespan`, `solution`, `energyRate`, `blowup_limsup`, `forceDifference_sobolev_bound/_negativeSobolev_tendsto` | `velocity_unique` | U5, U7; `SingularTrajectoryT`/`limsupLeft`/`speedENorm` | **yes** |
| U14 | `closureInEnergy` | (via U13) | — | U13; `RegularTrajectoryT` unpack | **yes** |
| U10 | `extendedProductDensity` | (via U7) | — | U7; `extendedBreakdownSetT` | **yes** |
| U11 | `projectionOntoInitialData` | (via U7) | — | U7, U10; `0∈forceClassT` | **yes** |
| U12 | `zeroInitialProjection` | (via U7) | — | U7, U10; `0∈initialClassT` | **yes** |

**T20 not consumed** (`prop:critical` feeds `cor:nondensity` = node T21). The `:586` `𝓧`-topology non-density
remark and `:591 rem:peaks` are **not** T19 fields (owner questions §3-§4 of `RECONCILIATION.md`).

## 3. Waves (≤ 3 concurrent per current lane cap)

| wave | units | sizes / models | status |
|---|---|---|---|
| W1 | **U1** threshold · **U2** mixed arith · **U3** region examples · **U6** zero-norms | S / S / S / S codex-sol | **unblocked today** (no T18) |
| W1′ | **U4** energy-time embedding · **U5** reference finite `E_T` | M / M codex-sol | **unblocked today** (pure Mathlib) |
| W2 | **U7** density engine → **U8** regular-reference exact-`T` · **U9** mixed density | L / M-L / M-L Opus | **gated on T18 U12** (U7 first; U8/U9 reuse its helper) |
| W3 | **U13** simultaneous pair convergence → **U14** closure inclusion | L Opus / M codex-sol | **gated on T18 U12** (U14 after U13) |
| W4 | **U10** product density · **U11** projection onto `𝓧` · **U12** `a=0` fibre | S-M / M / M codex-sol | **gated (via U7)**; after U7/U10 |
| W5 | assembly + registration (`Contracts/V1` T03 umbrella + `Bindings` + `Tests`, four contract ids) | M codex-sol | after all 13 fields |

Critical path: **T18 U12 → U7 → {U8, U9, U10} ; T18 U12 → U13 → U14 ; U7/U10 → U11/U12**. W1/W1′ (6 units, no
T18) are startable **now** and clear the whole arithmetic/bookkeeping bucket before the T18 gate opens. The
assembly lane (W5) bundles the four structures and closes the four `…Statement` defs; register every field
and stage the T18-gated tests behind T18 U12, exactly as R41/R46 staged theirs.

## 4. Risks

1. **T18 registration gap (highest, `RECONCILIATION.md` §4 owner Q1).** Every constructive field is blocked on
   T18 U12; if T18 registers as a `Contracts/V1` API the T19 proof consumes it as a registered fact (mirroring
   R46's `InsertionFamilyAPI`). Until then U7-U14 are lane-**writable** against the T18 field names but not
   closable. Do not weaken any field to unblock — stage, as T18 staged its T15/T17-gated fields.
2. **U4 `energyTimeEmbedding` (analytic long pole of W1′).** The `∫⁻ ≤ essSup·measure` step on
   `volume.restrict (Ioo 0 T)` + the `rpow (1/2)`/`ofReal (√T)` juggling is the only genuinely analytic unit
   with no named input; if the `essSup`-measure lemma name resists, escalate to Opus. It is self-contained
   (no Section 3 node) so it can be closed independently of the T18 gate.
3. **U13 reference-velocity identification (mirrors R41 `href`).** The `E_T` limit and the `RegularTrajectoryT`
   match require `reference.velocity = ins.v` on `[0,T)` via T11 `velocity_unique`; the `min (T+margin) (T+δ)`
   window bookkeeping (`Bindings/MainThresholds.lean:108-116`) must be reproduced exactly, or the energy
   congruence step fails.
4. **U11/U12 image equalities need an inhabited fibre.** `⊇` is the content: `projectionOntoInitialData` needs
   a force class inhabited at each `a` (`0∈forceClassT`), and `zeroInitialProjection` needs `0∈initialClassT`
   (the singleton must be inhabited, not `∅`). Both are T10/T11 data facts; confirm the torus
   `zero_mem_{forceClassT,initialClassT}` lemmas exist (whole-space twins at `Section4/A04/ZeroSolution.lean`)
   before starting W4.
5. **`Prop` vs `Type` (owner Q2).** All four structures are `Prop` (data-free, T24 precedent) vs the R41/R46
   `Type` registry convention; the assembly lane (W5) must confirm the sort before registering, or the four
   contract ids drift from the Section 4 twins' shape.
