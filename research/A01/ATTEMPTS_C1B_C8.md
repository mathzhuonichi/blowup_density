# ATTEMPTS — lane 124, row C1b-c8-0 (order-0 datum-path continuity) + c8 (m=0)

Module: `formalization/NSFormalization/Section4/A01/DatumPathContinuity.lean`.
All eight declarations `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(`research/A01/axioms_c1b_c8.lean`).  `lake build` and `lake env lean` (silent) OK,
`make check` OK.  Probe: `research/A01/probes/c1b_c8_probe.lean`.

## Route that worked (no new analysis, no missing Mathlib fact)

`orderZeroDatum hz` (`D01/OrderZeroDatum.lean:96`) is
`cyclesToAngularRealVector 0 (WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (componentLp hz i))))`.
Every factor is already a CLM/CLE in the tree, so `orderZeroDatumCLM` bundles them:

* `componentCLM i = (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).compLpL 2 volume`
  (`ContinuousLinearMap.compLpL`, `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:817`).
* `𝓕 = fourierCLM ℂ (Lp ℂ 2 volume)` (`Mathlib/Analysis/Fourier/Notation.lean:167`,
  `fourierCLM_apply` is `rfl`; the same instance `D01/SmoothDatum.lean:114` uses).
  Restricted to ℝ with `.restrictScalars ℝ` (coe is `rfl`) to get an ℝ-CLM.
* `realProjectionTo 0 : SobolevHilbert 0 →L[ℝ] RealSobolevHilbert 0`
  (`Paper3/RealPositiveDensity.lean:31`).  `SobolevHilbert 0 = Lp ℂ 2 volume` (abbrev),
  so it eats `𝓕 (…)` directly.
* `WithLp.toLp 2 = ⇑(PiLp.continuousLinearEquiv 2 ℝ _).symm` **by `rfl`**
  (`Mathlib/Analysis/Normed/Lp/PiLp.lean:1150`).  Assembly of the three components
  is `ContinuousLinearMap.pi (fun i => …)` into the plain `∀ i, RealSobolevHilbert 0`,
  then `(PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap`.
* `cyclesToAngularRealVector 0 : RealVectorSobolev 0 ≃L[ℝ] RealVectorSobolev 0`
  (`Paper3/AngularRealVectorBochner.lean:15`), via `.toContinuousLinearMap`.

`orderZeroDatum_memLp_eq` : the whole thing is `rfl` **except** the single step
`componentLp (Lp.memLp u) i = componentCLM i u`, which is proved by `Lp.ext`
(both sides agree a.e. with `x ↦ ((u x i : ℝ) : ℂ)`).  Proof shape:
`unfold orderZeroDatum; rw [key]; rfl`, where `key` rewrites that one step under the
`fun i => realProjectionTo 0 (𝓕 …)` binder.

`continuous_orderZeroDatum` (row C1b-c8-0 verbatim) then follows by rewriting the
path to `fun t => orderZeroDatumCLM (U t)` and composing `orderZeroDatumCLM.continuous`
with `hU`.  `datumPath`/`continuousOn_datumPath` give the `ContinuousOn (Ico 0 T)`
form for `U : C(Icc 0 T, EulerMeanSolenoidal.L2)`; `datumPath_isSobolevDatum` glues in
lane 119's `isSobolevDatum_zero_ordinaryL2` + `IsSobolevDatum.congr_field` under the
B1 hand-off `velocity t =ᵐ ⇑(U t)` (row C1b-rep) to state the m=0 case of the
`ClassicalSolutionR.sobolev` shape (`Data.lean:643`).

## Design decisions

* **Domain of `orderZeroDatumCLM` = `EulerMeanSolenoidal.L2`**
  (`= Lp Space 2 volume`, abbrev, `MeanSolenoidalSpace.lean:22`), so step 2 is a
  literal composition on `U : X → EulerMeanSolenoidal.L2` — **no coercion needed**.
* **`𝓕` via `restrictScalars ℝ` of the ℂ-CLM**, not a hypothetical
  `fourierCLM ℝ (Lp ℂ 2 volume)` (its `FourierSMul ℝ` instance was not needed and
  not checked); `restrictScalars` is guaranteed and keeps the map function `rfl`-equal.
* **`datumPath` totalised by `dite` (`0` off `Icc 0 T`)** because c8 wants a total
  `G : ℝ → RealVectorSobolev 0` while `U` lives on the subtype.  On `Ico 0 T` the
  `dite` reduces (proof irrelevance) to `orderZeroDatumCLM (U (inclusion ·))`.
* **B1 hand-off shape (row C1b-rep):** stated as
  `∀ t (ht : t ∈ Ico 0 T), (fun x => v (t,x)) =ᵐ[volume] ⇑(U ⟨t, Ico_subset_Icc ht⟩)`.
  This is the cleanest form: `IsSobolevDatum.congr_field` needs exactly an a.e.
  equality between the velocity slice and `⇑(U t)`, no pointwise/`Icc`-endpoint data.

## Failures / friction (exact text) and fixes

1. **`RealSobolevHilbert` unknown identifier** (`c1b_c8_probe.lean:16`):
   `error(lean.unknownIdentifier): Unknown identifier RealSobolevHilbert`.  It is
   `NSFormalization.Source.RealSobolev.RealSobolevHilbert` (`= realSubspace s`,
   `RealSobolev.lean:121`, a `ClosedSubmodule` coerced to a type).  Fixed by
   `open NSFormalization.Source.RealSobolev (RealSobolevHilbert)`.

2. **`rw [h2]` failed to find the `compLpL` pattern** because the goal held `(Ci i) u`
   (a `def`) not the unfolded `compLpL … u`:
   `Tactic rewrite failed: Did not find an occurrence of the pattern
   ↑↑((ContinuousLinearMap.compLpL 2 volume (…)) u) x`.  Fixed by `simp only [componentCLM]`
   before `rw [h1, h2]`; the residual `((u x i:ℝ):ℂ) = (ofRealCLM ∘SL proj i) (u x)`
   closes by `rfl`.

3. **Deprecations broke silence** (the gate wants `lake env lean` silent):
   `continuousOn_iff_continuous_restrict`→`continuousOn_iff_continuous_domRestrict`,
   `Set.restrict`/`Set.restrict_apply`→`Set.domRestrict`/`Set.domRestrict_apply`,
   `dif_pos`→`dite_eq_left` (deprecated 2026-07-21, `Init/Core.lean:1210`; same
   signature `dite_eq_left (hc : c) : dite c t e = t hc`).  After switching, the
   `rw [continuousOn_iff_continuous_domRestrict]` goal uses `domRestrict`, so the
   congruence lemma `hEq` must also be stated with `domRestrict`.

4. **`‹_›` in the `hv` binder** could not synthesise `t ∈ Ico 0 T`
   (`Tactic assumption failed ⊢ t ∈ Set.Ico 0 T`): the anonymous proof term inside the
   hypothesis type has no such local hyp.  Fixed by a **named** binder
   `∀ t (ht : t ∈ Set.Ico 0 T), …`.

5. **Dot notation `(isSobolevDatum_zero_ordinaryL2 …).congr_field` would fail** (review
   119 finding 12: the helper is declared in `…A01` but the predicate's head constant is
   `…D01.IsSobolevDatum`).  Used the explicit application
   `IsSobolevDatum.congr_field (…) (…)`; it resolves to `A01.IsSobolevDatum.congr_field`
   because the module is in `namespace …A01`.

6. **axioms-file `example`s**: `orderZeroDatum` needed opening; a stray `_` placeholder
   in `Lp.memLp ((fun _ => c) _)` gave `don't know how to synthesize implicit argument z`.
   Rewrote as `Lp.memLp c` / `Lp.memLp u` (constant and identity paths).

## No MAINT flag

No missing Mathlib/tree fact about the realization maps was hit; every CLM/CLE was
already present.  Nothing needed a bridging lemma in a foreign module.

## Review follow-up (lane 124 ACCEPT-WITH-NOTES, `research/A01/REVIEW_C1B_C8.md`)

**Injectivity spin-off (findings 6/7).** The reviewer proved
`orderZeroDatumCLM_injective : Function.Injective orderZeroDatumCLM` (45 lines,
`[propext, Classical.choice, Quot.sound]`); copied verbatim, credited, into
`research/A01/probes/orderZeroDatumCLM_injective_probe.lean` (compiles here,
exit 0).  It is the natural **uniqueness** input for the still-open row
`C1b-unique` (order-0 datum determined by the field), and the cheap half of the
missing **order-0 Plancherel identity** `‖orderZeroDatum hz‖ = ‖z‖_{L²}`
(`D01/OrderZeroDatum.lean:40-53`).  Recommend a follow-up SIMP/D01 lane promote it
into the tree; the probe file is the reconstructible source.  The probe also
carries the concrete non-constant witness `t ↦ orderZeroDatum (Lp.memLp (t • u₀))`
with `u₀ = indicatorConstLp (ball 0 1) e₀` (different values at `t=0,1`).

**MAINT (finding 8): `componentCLM`/`orderZeroDatumCLM` are D01-level, not A01.**
Both mention nothing from A01, nothing from Euler, nothing from the carrier
bridge — `EulerMeanSolenoidal.L2` is a bare `abbrev` for `Lp Space 2 volume`
(`Euler/MeanSolenoidalSpace.lean:22`), and the committed probe
`research/A01/probes/c1b_c8_probe.lean` builds the identical map with domain
literally `Lp Space 2 (volume : Measure Space)`.  In a later **MAINT lane** they
(and `componentLp_eq_compLpL`, `orderZeroDatum_memLp_eq`, `continuous_orderZeroDatum`)
should move next to `orderZeroDatum` in `Section4/D01/OrderZeroDatum.lean`, leaving
A01 with only `datumPath` / `continuousOn_datumPath` / `datumPath_isSobolevDatum`
(the parts that actually mention the `exists_local` carrier).  Not done in this
lane: it would put a D01 edit inside an A01 PR.

**Brief for B1 (finding 9): the hand-off `hv` is faithful but must be built.**
`datumPath_isSobolevDatum`'s hypothesis
`(fun x => v (t,x)) =ᵐ[volume] ⇑(U ⟨t, …⟩)` on `Ico 0 T` is exactly row `C1b-rep`
(a.e., not pointwise; `Ico`, not `Icc`; the raw `⇑(U t)`, not
`ordinaryLift`/`value`; the first half of `C1b-rep`, leaving `velocity(0,·)=a.field`
for `initial`).  **But** the tree's existing "spacetime velocity ↔ `L²` path"
lemmas have a *different* shape: `Source/CompactSlabSobolev.lean:99-102`,
`Source/InsertionSobolev.lean:25-27`, `Source/PhysicalIntegerSobolev.lean:76-78`
all state **pointwise** equality against a `SmoothL2Field` path with premise
`∀ n, Continuous (fun t => (U t).jetLp n)`.  Converting those to lane 124's `hv`
needs `U t = (A t).toLp` + `SmoothL2Field.toLp_ae` (`Euler/LpSmoothField.lean:44`),
which `exists_local` gives **only at `t = 0`** (`Source/OrdinaryForcedLocal.lean:41`,
`U ⟨0,…⟩ = a.toLp`); no clause identifies `U t` with any smooth field's `toLp` for
`t > 0`.  The only per-slice a.e. identification in the tree,
`EulerMeanSmoothRepresentative.representative_ae`
(`Euler/MeanSmoothRepresentative.lean:92`), needs `SmoothOrbit (U t)` (not produced
by `exists_local`) and gives no time-continuity of the representative.  So B1 must
**construct** `hv`, not inherit it.  This same `∀ j, Continuous (fun t => (A t).jetLp j)`
is also the order-`m` continuity blocker (row `C1b-c8-m`, above).
