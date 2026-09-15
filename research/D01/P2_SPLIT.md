# D01 obligation P2 — the split from the L² Helmholtz decomposition to `SmoothSquareIntegrableJets (∇p(t,·))`

> **P2 COMPLETE (lane 117), modulo contract registration.**  SL8's target is proved unconditionally
> as `NSFormalization.Section4.D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`
> in `formalization/NSFormalization/Section4/D01/PressureJets.lean`:
> for `u : ClassicalSolutionR ν a f T`, `hf : MemForceR f`, `t ∈ Ioo 0 T`,
> `SmoothSquareIntegrableJets (fun x => pressureGradient u.pressure t x)` — this is
> `Contracts.V1.SmoothSquareIntegrableJets` by the `rfl` bridge in `Bindings/DatumLemmas.lean:61-62`
> (checked in `research/D01/axioms_sl8_assembly.lean`).  Order-0 seed = `orderZeroDatum_pressureGradient_eq`
> (SL8 row i.7); corollary `temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR` gives
> `∂ₜu(t,·) ∈ H^∞`.  All axioms standard.  See `research/D01/SL8_SPLIT.md` and
> `research/D01/ATTEMPTS_SL8_ASSEMBLY.md`.  Remaining for P2: register the P2 contract field/binding.

Lane 062, task **D01**, obligation **P2** (from lanes 050/055, `PLAN.md §8`).
Split-and-start document: the precise chain of sub-lemmas, each with a Lean-ready statement
in *our* vocabulary and an S/M/L cost + blocker.  **Revised after `research/D01/REVIEW_P2.md`
(ACCEPT-WITH-NOTES, findings 1–4).**  The S-level piece (fiber-symbol algebra, sub-lemma SL1)
is proved in this lane: `formalization/NSFormalization/Section4/D01/LeraySymbol.lean`
(`research/D01/axioms_p2.lean`, all standard axioms).  No `sorry`, no `axiom`.

> **What the first draft got wrong (fixed here).**  (1) SL3 was called "missing
> infrastructure / M crux": false — a coordinate-mixing, operator-valued `L²` multiplier
> from *this exact symbol* already exists in the vendored library this module imports
> (`R3LerayPointwiseL2.lean`), and `ContinuousLinearMap.holderL` is not scalar-only.
> (2) SL4β (= D01 unit **L3**, closed solenoidal subspace) was called a hard **L** blocker on
> the critical path: it is **not needed** — route B defines `P` by its symbol, so "kills a
> solenoidal field" is a one-line pointwise fibre fact (now proved in `LeraySymbol.lean`).
> (3) The sub-lemma the chain actually stalls on — a non-circular *entry point* that produces
> a datum rather than transforming one — was missing; SL7 below adds it.

## Target

For `u : ClassicalSolutionR ν a f T`, `hf : MemForceR f`, `t ∈ Ioo (0:ℝ) T`:
```lean
SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x)
```
`Space = EuclideanSpace ℝ (Fin 3)` (`ProblemStatement.lean:30`), definitionally HeliCorgi's
`MNS2.R3`.  `SmoothSquareIntegrableJets`, `IsSobolevDatum`, `sobolevENorm`, `RealVectorSobolev`,
`MemForceR`, `ClassicalSolutionR` are the A02/D01 restatements, defeq to `Contracts/V1/Data.lean`.
The "order-`s`, angular convention" content of `RealVectorSobolev` / `IsSobolevDatum` lives in
`angularRealization` (`Data.lean:160`; `IsSobolevDatum`'s realization map), **not** in the
type: `RealSobolevHilbert _s = realSubspace _s` ignores its order argument, so the datum type is
convention-neutral and `RealVectorPositiveDensity.lean:15` ("cycles-frequency … angular transport
a separate obligation") and the "angular" reading are both defensible — cite `angularRealization`,
not `:15`, for the convention.

## What is already in place (lane 055, `Section4/D01/Pressure.lean`) — reduction, not gap

`pressureGradient_slice_smoothSquareIntegrableJets` reduces P2 to a **single** input,
`SmoothSquareIntegrableJets (∂ₜu(t,·))`; `pressureGradient_slice_smoothL2_iff_temporalDerivative`
(`:362`) proves the two are interderivable through `momentum` given
```
h(t,·) := f(t,·) − (u·∇)u(t,·) + νΔu(t,·)   ∈ H^∞   (proved H^∞ in 055):
  forceSlice_smoothL2_of_memForceR, advection_slice_smoothL2, laplacian_slice_smoothL2
  + smoothL2_add/smoothL2_sub/smoothL2_const_smul.
```
055 proves only the *equivalence*, neither side outright (`Pressure.lean:362`), and no field of
`ClassicalSolutionR` supplies a datum for `∂ₜu` or `∇p` at positive order
(`DatumToJets.lean:499-503`).  So P2 = "produce `SmoothSquareIntegrableJets (∇p(t,·))` from
`h ∈ H^∞`", honest route (`Data.lean:621`, eq:Rpressure):
```
∇p(t,·) = (I−P) h(t,·),      ∂ₜu(t,·) = P h(t,·).
```

## Route — B (angular symbol multiplier) and A (HeliCorgi L²) build the same operator

`(I−P)` is the componentwise Fourier multiplier by the **real, angular, 0-homogeneous** fiber
symbol `complementSymbol ξ = ξξᵀ/‖ξ‖²` (proved here).  Because the symbol is **0-homogeneous**
(`complementSymbol_smul`, this lane) it commutes with the cycles↔angular frequency **dilation**,
and the radial Sobolev weight is scalar so it commutes with any matrix symbol.  Hence route A
(HeliCorgi's cycles `L²` operator) and route B (native angular) build the **same** operator, and
either convention may be used — the transport the first draft worried about is *free*.
HeliCorgi's `MNS2.r3HelmholtzPressure_gradient` (`R3HelmholtzPressure.lean:259`, `∂ⱼp = −((I−P)F)ⱼ`
in 𝓢') is the order-0 identity and is the natural cross-check for SL8, **not** demoted.

## Sub-lemmas (SL1–SL8; SL0 = done in 055)

| # | (task) | statement (short) | cost | blocker |
|---|--------|-------------------|------|---------|
| SL0 | — | `h = f−(u·∇)u+νΔu ∈ H^∞`; P2 ⇔ `∂ₜu(t,·) ∈ H^∞` | **done (055)** | — |
| **SL1** | **d1,a** | `complementSymbol ξ = ξξᵀ/‖ξ‖²` — projection, opNorm ≤ 1, real, even, **0-homog**, kills transverse, fixes longitudinal | **S — DONE (this lane)** | — |
| SL2 | a | land the multiplier in the real subspace `RealVectorSobolev` (via `realProjectionTo`); even+real ⇒ preserves it | **DONE** (073 `realSymmetryVec_lerayComplementL2`, 081 `image_component_mem_realSubspace`; reality built into the codomain of `lerayComplement s`) | — |
| SL3 | d2 | operator-valued `L²` multiplier `RVSᵐ →L[ℝ] RVSᵐ`, opNorm ≤ 1, a.e. `= complementSymbol ξ (·)` | **DONE** (073 `D01/LerayMultiplier.lean` raw carrier + bridge; 081 `D01/LerayDatum.lean` `lerayComplement s`, PR #82) | — |
| SL4 | c1 | `div ∂ₜu(t,·)=0` (α); `(I−P)` kills a solenoidal field (fibre fact, **done SL1**) | α: S/M | α **proved** (lane 074, `D01/DivergenceTime.lean`); Fourier form **proved abstractly** (lane 079, `D01/Transverse.lean` `transverse_of_divergence_free`, for any divergence-free `SmoothL2Field`; 074's lemma feeds it by `rfl`). **Sequencing (079 review F5):** the `SmoothL2Field` wrapper of `∂ₜu(t,·)` is equivalent under `MemForceR f` to P2's own target (`Pressure.lean`), so the `∂ₜu` instance must come AFTER SL7's non-circular order-0 seed, not before. **SL4β/unit L3 DELETED — not needed** |
| SL5 | c2 | `∇p` longitudinal via **curl-freeness** (Clairaut), so `(I−P)∇p = ∇p` (fibre fact, **done SL1**) | M | needs SL6 (`iξⱼ` datum) |
| SL6 | d | **the one substantive lemma:** `IsSobolevDatum m (∂ⱼz) (iξⱼ·A)` from `IsSobolevDatum m z A` | **DONE** (066 `D01/DerivativeDatum.lean:245` `isSobolevDatum_partialDeriv`, for `Z : SmoothL2Field`, order `m+1 → m`) | — |
| SL7 | b,c3 | eq:Rpressure at every order, **non-circular**: order-0 Plancherel seed + `pressure_gradient` + bootstrap | S/M (seed) + M | order-0 `MemLp⟹IsSobolevDatum 0` constructor not yet wired |
| SL8 | e | pin datum → classical field, feed `DatumToJets` ⇒ `SmoothSquareIntegrableJets (∇p)` | **DONE (117)** — `PressureJets.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`; assembly route (rows i.7 → ii → iii via `orderZeroDatum`/`lowerVectorL`/`isSobolevDatum_lower_iff`), not the `representative_ae` route | — |

**Bottom line (finding 4 rewrite).**  P2 is **not** gated by any **L** piece.  Its three genuine
work items are all S/M: **SL7's order-0 Plancherel seed**, **SL6 (`iξⱼ` datum)**, and **SL3**
(largely written upstream) — plus **SL4α** (`div ∂ₜu = 0`, S/M).  SL4β (= unit L3) has been
removed from the critical path; SL1/SL2/SL5's fibre content is proved.  Everything else is M
assembly.  (SmoothSquareIntegrableJets is qualitative, so any `opNorm ≤ C` suffices downstream —
no constant is consumed by SL6–SL8; the matrix route gives `≤ 1` for free anyway.)

## Lean-ready statements

### SL1 (task d1, a) — S, DONE (this lane, `Section4/D01/LeraySymbol.lean`)
```lean
namespace NSFormalization.Section4.D01.Leray
def complementSymbol (ξ : Space) : Space →L[ℝ] Space := (ℝ ∙ ξ).starProjection
theorem complementSymbol_apply (ξ v) : complementSymbol ξ v = (inner ℝ ξ v / ‖ξ‖ ^ 2) • ξ   -- ξξᵀ/‖ξ‖²
theorem complementSymbol_idempotent (ξ v) : complementSymbol ξ (complementSymbol ξ v) = complementSymbol ξ v
theorem complementSymbol_opNorm_le_one (ξ) : ‖complementSymbol ξ‖ ≤ 1
theorem norm_complementSymbol_le (ξ v) : ‖complementSymbol ξ v‖ ≤ ‖v‖
theorem complementSymbol_neg (ξ) : complementSymbol (-ξ) = complementSymbol ξ            -- even
theorem complementSymbol_smul (c) (hc : c ≠ 0) (ξ) : complementSymbol (c • ξ) = complementSymbol ξ  -- 0-homog
theorem leraySymbol_add_complementSymbol (ξ v) : MNS2.r3LeraySymbol ξ v + complementSymbol ξ v = v  -- P+(I−P)=I
-- fibre facts (SL4/SL5 bypass of unit L3):
theorem complementSymbol_eq_zero_of_inner_eq_zero (ξ v) (h : inner ℝ ξ v = 0) : complementSymbol ξ v = 0
theorem complementSymbol_smul_self (c) (ξ) : complementSymbol ξ (c • ξ) = c • ξ
```
`ξ = 0`: `ℝ ∙ 0 = ⊥`, so `complementSymbol 0 = 0` (matches upstream `r3LeraySymbol_zero = id`);
`{0}` null ⇒ multiplier-irrelevant (documented in the module).

### SL2 (task a) — S/M — the reality subspace
```lean
-- built to land in the real subspace by construction (pattern realProjectionTo):
def lerayComplementVectorL (m : ℝ) : RealVectorSobolev m →L[ℝ] RealVectorSobolev m
-- and: on data already real, the raw multiplier and its real-projected form agree
--   (even + real ⇒ commutes with realSymmetry, so the real subspace is invariant).
```
`RealVectorSobolev m = Product (Fin 3) (RealSobolevHilbert m)` = the `realSymmetry`-fixed subspace
of `Lp ℂ 2` triples; `complementSymbol` real (`→L[ℝ]`) + even ⇒ commutes with `realSymmetry`
(`Source/RealSobolev.lean:92,118`).  May be absorbed into SL3's codomain via `realProjectionTo`
(`Paper3/RealPositiveDensity.lean:31`, `opNorm ≤ 1` at `:44`).  **Blocker:** needs SL3 object.

### SL3 (task d2) — S/M — the operator-valued multiplier (NOT new infrastructure)
```lean
theorem lerayComplementVectorL_opNorm_le (m : ℝ) : ‖lerayComplementVectorL m‖ ≤ 1
theorem lerayComplementVectorL_isSobolevDatum {m z A} (hA : IsSobolevDatum m z A) :
    IsSobolevDatum m (fun x => complementField z x) (lerayComplementVectorL m A)
```
**Two ready construction templates, either giving the bundled CLM + `opNorm ≤ 1` + a.e. action:**
- **HeliCorgi's own worked example** — `vendor/HeliCorgi/Formal/R3LerayPointwiseL2.lean`: the
  coordinate-mixing operator-valued `L²` multiplier from *this symbol*, ~60 lines, **no**
  `holderL`, **no** `ContinuousLinearMap.pi`.  `memLp_r3LerayPointwiseAction` gets `MemLp … 2` and
  `‖·‖ ≤ ‖·‖` in one line via `(Lp.memLp f).of_le … (fun ξ => norm_r3LeraySymbolComplex_le …)`;
  `r3LerayPointwiseL2_ae` is the a.e. action.  The complement is `r3LerayComplementL2 = F − P F`
  (`R3HelmholtzPressure.lean:228`), with `fourier_r3LerayComplementL2_ae` its longitudinal symbol.
- **Mathlib `ContinuousLinearMap.holderL`** (`Mathlib/MeasureTheory/Function/Holder.lean:125`,
  `norm_holderL_le : ‖B.holderL …‖ ≤ ‖B‖`) with the **operator-valued** input
  `B := ContinuousLinearMap.id ℝ (R3C →L[ℝ] R3C)` (evaluation `E →L (F →L G)` with `E = F →L G`),
  `‖B‖ ≤ 1` by `ContinuousLinearMap.norm_id_le`.  `B.holderL volume ⊤ 2 2 S` (`S` = the symbol in
  `Lp (R3C →L[ℝ] R3C) ⊤`) yields the CLM; `.norm_holder_apply_apply_le` gives `opNorm ≤ 1`;
  `.coeFn_holder` the a.e. action — **one step**, from the single input `MemLp (symbol) ⊤ volume`
  (bound = SL1's `complementSymbol_opNorm_le_one`; measurability = HeliCorgi's
  `aestronglyMeasurable_r3LerayPointwiseAction`).  `holderL` was **never** scalar-only.
The **complex** fibre algebra SL3 actually consumes (data are ℂ-valued) already exists upstream:
`R3LerayComplexFiberSymbol.lean` (`r3LeraySymbolComplex : R3C →L[ℂ] R3C`, `_apply`, `_idempotent`,
`_fixed_of_mem`, `_mem`, `norm_…_le`); the ℝ module here is the "real matrix entries / reality"
statement (SL2).  **The one genuine (small) SL3 work item:** `Source/FiniteHilbertBochner.lean:42,44`
`assemble`/`coordinates` (with `assemble_coordinates :47`) bridging
`RealVectorSobolev m = Product (Fin 3) (RealSobolevHilbert m)` (a `PiLp 2` *of* `Lp`) and
`Lp (EuclideanSpace ℂ (Fin 3)) 2` (the `Lp` *of* a `PiLp 2`, where the pointwise matrix acts) is not
yet known to be an **isometry at `q = 2`** (only `approximation_bound :64`).  **Drop the nine
scalar-entry route:** assembling nine `ξᵢξⱼ/‖ξ‖²` `holderL` entries with `ContinuousLinearMap.pi`
reaches `opNorm ≤ 1` only through a 9-term triangle inequality (`≤ 3`, never `≤ 1`) — the constant
`1` is the pointwise matrix fact `‖M(ξ)v‖ ≤ ‖v‖` and survives only in the vector-valued picture.

### SL4 (task c1) — α: S/M; β (unit L3): **DELETED, not needed**
```lean
-- planned name (ill-typed sketch; delivered as `spatialDivergence_temporalDerivative_eq_zero` on the pair-form field, lane 074)
theorem div_temporalDerivative_eq_zero {ν a f T} (u : ClassicalSolutionR ν a f T)
    {t} (ht : t ∈ Ioo (0:ℝ) T) (x : Space) :
    (∑ i, spatialDerivative (fun y => temporalDerivative u.velocity t y) i x i) = 0
-- ∑ᵢ ∂ᵢ(∂ₜuᵢ) = ∂ₜ(div u) = ∂ₜ 0 = 0, using velocity_smooth (Clairaut) + u.divergence_free.
-- "(I−P) kills a solenoidal field" is then the fibre fact, DONE in SL1:
--   div z = 0  ⟹ ⟪ξ, ẑ(ξ)⟫ = 0 a.e. (via SL6)  ⟹  complementSymbol_eq_zero_of_inner_eq_zero.
```
The closed solenoidal subspace (HeliCorgi builds `P` that way, `R3LerayL2Operator.lean:28`) is
required only if `P` is *defined* as its projection.  Route B defines `P` by symbol, so the
kill-solenoidal step is `complementSymbol_eq_zero_of_inner_eq_zero` (SL1) composed with SL3's a.e.
action (upstream's exact shape: `R3LerayComplexDivergenceBridge.lean:23,54`).  **Unit L3 leaves the
critical path.**  SL4α proved in lane 074 (PR #75). Remaining for SL4: the Fourier transverse form via D2 + `isSobolevDatum_partialDeriv` (needs a `SmoothL2Field` wrapper of the slice and the `m+1 → m` order bookkeeping) + `complementSymbol_eq_zero_of_inner_eq_zero`.

### SL5 (task c2) — M — gradient longitudinal via curl-freeness (not a datum for `p`)
```lean
-- curl-freeness of ∇p (Clairaut on smooth p; no decay/datum for p needed — pressure_smooth only):
theorem pressureGradient_curl_free … : ∂ᵢ(∂ⱼp) = ∂ⱼ(∂ᵢp)
-- Fourier side (via SL6):  ξᵢ (∇p)^ⱼ = ξⱼ (∇p)^ᵢ a.e.  ⟹  (∇p)^(ξ) ∈ ℝ ∙ ξ  ⟹
theorem lerayComplementVectorL_pressureGradient {A m} (hA : IsSobolevDatum m (fun x => ∇p x) A) :
    lerayComplementVectorL m A = A                     -- (I−P) fixes ∇p (complementSymbol_smul_self)
```
First draft used `∇p̂(ξ) = iξ p̂(ξ)`, which presupposes a datum for `p` — **wrong invariant**
(`ClassicalSolutionR` gives `p` no decay, only `pressure_smooth`).  The right invariant is
curl-freeness, whose Fourier form `ξᵢ ẑⱼ = ξⱼ ẑᵢ` (⟹ `ẑ(ξ) ∈ ℂ∙ξ`) is exactly the hypothesis of
the fix-longitudinal fibre fact (`complementSymbol_smul_self`, SL1).  **Blocker:** SL6.

### SL6 (task d) — M — the one substantive analytic lemma
```lean
-- iξⱼ is the angular-convention Fourier symbol of ∂ⱼ; on order-m data it is the bounded
-- order-lowering multiplier |ξⱼ|(1+‖ξ‖²)^{-1/2} ≤ 1 (SobolevDirectionalDerivative pattern):
theorem isSobolevDatum_partialDeriv {m : ℝ} {z : Space → Space} {A : RealVectorSobolev m}
    (hA : IsSobolevDatum m z A) (j : Fin 3) :
    IsSobolevDatum m (fun x => partialDeriv j z x) (freqMulI j A)
```
where `freqMulI j` multiplies the (order-m weighted) datum componentwise by `iξⱼ` (well-defined in
`Lp` because on order-m weighted data the effective multiplier is the **bounded**
`iξⱼ(1+‖ξ‖²)^{-1/2}`; needs `z ∈ H^{m+1}`, supplied by `h ∈ H^∞`).  This single lemma yields SL4's
Fourier form (`div z = 0 ⟹ ⟪ξ,ẑ⟫ = 0`) **and** SL5's longitudinality.  **Scalar building block
exists:** `Paper3/SobolevDirectionalDerivative.lean:56` (a `holderL` multiplier with symbol
`iξⱼ(1+‖ξ‖²)^{-1/2}`); the `IsSobolevDatum`-level vector statement is the new part.  Rate **M**.

### SL7 (task b, c3) — S/M + M — eq:Rpressure at every order, non-circular
```lean
-- (7a, NEW, the missing entry point) order-0 Plancherel datum existence:
theorem exists_isSobolevDatum_zero_of_memLp {z : Space → Space}
    (hz : MemLp z 2 volume) (hzc : ContinuousOn …) : ∃ A : RealVectorSobolev 0, IsSobolevDatum 0 z A
-- (7b) seed: ClassicalSolutionR.pressure_gradient (SolutionClass.lean:137) gives ∇p(t,·)'s
--     order-0 datum for free; ∂ₜu = h − ∇p gives its order-0 datum by subtraction.  At order 0
--     the SL4/SL5 fibre argument is non-circular: lerayComplementVectorL 0 (A⁰_h) = A⁰_{∇p}.
-- (7c) bootstrap: the 0-homog matrix symbol commutes with the scalar order weight, so
--     angularRealization m ∘ Q = Q_dist ∘ angularRealization m for every m
--     (shape of sobolevRealization_orderLowering, SobolevOrderLowering.lean:78); hence
theorem pressureGradient_isSobolevDatum {ν a f T} (u : ClassicalSolutionR ν a f T)
    (hf : MemForceR f) {t} (ht : t ∈ Ioo (0:ℝ) T) (m : ℝ) :
    ∃ A : RealVectorSobolev m, IsSobolevDatum m (fun x => pressureGradient u.pressure t x) A
```
This is the fix for finding 3: SL1–SL5 all *transform* data; nothing manufactures the first one.
`Section4/D01/SmoothDatum.lean:290` (`exists_isSobolevDatum_of_contDiff_memLp`) demands **all** jets
(`SmoothL2Field`), so it cannot seed order 0.  Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ`
(used upstream in `R3HelmholtzPressure.lean`) supplies the order-0 isometry; wiring it to
`IsSobolevDatum 0` is 7a.  The **L² decomposition `F = P F + (I−P) F` of task (b)** is
`leraySymbol_add_complementSymbol` (SL1) lifted through the two multipliers; its order-0 shadow is
HeliCorgi's `r3LerayComplementL2`.  **Blocker:** 7a (order-0 constructor), SL3, SL6.

### SL8 (task e) — M — distributional → classical, and the final theorem
```lean
theorem pressureGradient_representative_ae … :
    (fun x => angularBoundedRepresentative m hm (A i) x) =ᵐ[volume]
      fun x => ((pressureGradient u.pressure t x i : ℝ) : ℂ)
theorem pressureGradient_slice_smooth {ν a f T} (u : ClassicalSolutionR ν a f T)
    (hf : MemForceR f) {t} (ht : t ∈ Ioo (0:ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x)
```
Pattern: `A03.representative_ae` (`A03/ScalarTameProduct.lean:156`) +
`angularRealization_boundedRepresentative` (`AngularTameProduct.lean:146`) pin SL7's order-m datum
to the classical field a.e.; `DatumToJets.memLp_iteratedFDeriv_of_isSobolevDatum` (used in 055)
converts the order-m datum to order-`j` jets for every `j ≤ m`, and `contDiff_pressureGradient_slice`
(`DatumToJets.lean:504`) gives smoothness — the shape of 055's `advectionOf_smoothL2`.  Cross-check
against HeliCorgi's order-0 `r3HelmholtzPressure_gradient` (`R3HelmholtzPressure.lean:259`).
Equivalently, obtain `∂ₜu = P h` and feed 055's `pressureGradient_slice_smoothSquareIntegrableJets`.
**Blocker:** SL3–SL7.

## (a)–(e) ↔ SL map
- (a) reality/convention bridge = SL2 (symbol real+even+0-homog is SL1, done; the convention
  transport is *free* by 0-homogeneity, so no cycles↔angular bridge is on the critical path).
- (b) `L²` Helmholtz `F = PF + (I−P)F` = `leraySymbol_add_complementSymbol` (SL1) lifted through
  SL3; order-0 = HeliCorgi's `r3LerayComplementL2`; `PF` solenoidal / `(I−P)F` gradient = SL4/SL5.
- (c) `∇p = (I−P)(f−∇·(u⊗u))`: `(I−P)` kills solenoidal (SL4, fibre fact done), fixes gradients
  (SL5, fibre fact done), via the `iξⱼ` datum lemma (SL6), assembled at every order (SL7).
- (d) `(I−P)` bounded on `Hᵐ`, `ξξᵀ/‖ξ‖²` norm ≤ 1 = SL1 (symbol, done) + SL3 (CLM, upstream template).
- (e) distributional → classical pin = SL8.

## Reuse inventory (what exists, in which convention)
- **HeliCorgi, real angular symbol** — `MNS2.r3LeraySymbol ξ : R3 →L[ℝ] R3 = ((ℝ∙ξ)ᗮ).starProjection`
  (`R3LerayFrequencySymbol.lean`, Mathlib-only, compiles at this pin).  **Reused in SL1.**
- **HeliCorgi, operator-valued `L²` multiplier (the SL3 template)** — `R3LerayPointwiseL2.lean`
  (`r3LerayPointwiseAction`, `memLp_r3LerayPointwiseAction` via `MemLp.of_le`, `r3LerayPointwiseL2`,
  `r3LerayPointwiseL2_ae`); the complex fibre algebra `r3LeraySymbolComplex`
  (`R3LerayComplexFiberSymbol.lean`), divergence bridge (`R3LerayComplexDivergenceBridge.lean:23,54`),
  Fourier conjugation (`R3LerayPointwiseProjectionIdentification.lean`,
  `fourier_r3LerayL2Operator_ae`).
- **HeliCorgi, order-0 complex cycles** — `r3LerayL2Operator` (`R3LerayL2Operator.lean`, `P`, norm ≤ 1),
  `r3LerayComplementL2 = F − PF` (`R3HelmholtzPressure.lean:228`), `r3HelmholtzPressure` (`:223`),
  `r3HelmholtzPressure_gradient` (`:259`, `∂ⱼp = −((I−P)F)ⱼ` in 𝓢'), `fourier_r3LerayComplementL2_ae`.
  Cross-check for SL8 (not demoted).  `r3LerayL2OperatorReal` (`R3LerayRealLinearBridge.lean`).
- **Mathlib** — `ContinuousLinearMap.holderL` (`Holder.lean:125`, operator-valued OK) + `norm_holderL_le`
  + `norm_id_le`; `MeasureTheory.Lp.fourierTransformₗᵢ` (order-0 Plancherel isometry, SL7a).
- **Paper3 / Source templates** — `sobolevOrderLowering` (`:26,31,56`, scalar `holderL`);
  `SobolevDirectionalDerivative.lean:56` (scalar `iξⱼ(1+‖ξ‖²)^{-1/2}` block, SL6);
  `sobolevRealization_orderLowering` (`SobolevOrderLowering.lean:78`, SL7c bootstrap shape);
  `realProjectionTo` (`RealPositiveDensity.lean:31`, SL2); `FiniteHilbertBochner.assemble/coordinates`
  (`:42,44,47`; `q=2` isometry `:64` the SL3 work item); `realSymmetry`/`realProjection`/`realSubspace`
  (`Source/RealSobolev.lean:92,118`); `angularBoundedRepresentative`/`angularRealization_boundedRepresentative`
  (`AngularTameProduct.lean:141,146`); `A03.representative_ae` (`ScalarTameProduct.lean:156`).
- **DatumToJets** — `memLp_iteratedFDeriv_of_isSobolevDatum`, `smoothSquareIntegrableJets_slice`,
  `contDiff_pressureGradient_slice` (`:504`); `exists_isSobolevDatum_of_contDiff_memLp` (`:290`,
  all-jets only — cannot seed order 0, hence SL7a).
- **HeliCorgiPort.lean** — exposes six raw `example :=` references (four local-existence / NS-equation
  + `r3HelmholtzPressure`, `r3HelmholtzPressure_gradient`); **no** bridge to `RealVectorSobolev`/angular.
- **Periodic Leray (not applicable)** — `Source.ForcedCylinderLocal.leray` (`:26`),
  `Paper1.PeriodicLeray*`, `Paper1.PeriodicPressureSymbolOperator.pressureOperator`.
