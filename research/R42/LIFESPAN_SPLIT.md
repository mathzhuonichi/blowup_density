# R42 lifespan clauses — sub-lemma split (lane 072, task R42 split-and-start)

> Revised after review (`research/R42/REVIEW_LIFESPAN.md`): findings 1–5 applied.
> The stale "no additivity lemma" / "F_R+C_c^∞ not proved" claims (inherited from
> `research/R42/ATTEMPTS.md §5`, pre lane 028) are corrected; #3 and the strict
> half of #6 are re-sized to **S** and are now **proved** in `Lifespan.lean`.

Target: inhabit the **unregistered** `Contracts.V1.InsertionLifespanAPI`
(`verification/Contracts/V1/InsertionFamily.lean:421-436`; three fields —
`family`, `referenceLifespan`, `lifespan` — carrying the **two** lifespan clauses):

* `lifespan  : ∀ ε ∈ Ioc 0 family.ε₀,`
  `  Data.maximalLifespanR ν family.a (family.force ε) = ENNReal.ofReal family.T`
  — `T^ν_{max,R}(a, g_ε) = T` (`04-whole-space.tex:34`);
* `referenceLifespan :`
  `  ENNReal.ofReal (family.T + family.margin) < Data.maximalLifespanR ν family.a family.g`
  — `T + δ < T^ν_{max,R}(a, g)` (`04-whole-space.tex:32`).

Here `family.T = scaling.correction.T` (the shifted packet singular time; the
packet's own normalization is `T = 1`, `PacketAPI.speed_unbounded :
SpeedUnboundedAtOne`, `Contracts/V1/Packet.lean:242`) and
`family.margin = scaling.correction.δ`.

Reused registered interfaces (all in `verification/Contracts/V1/`):
`MaximalPartial.MaximalPartialAPI` — `lifespan_le_of_unbounded`,
`lifespan_ge_of_forall_shorter`, `referenceLifespan`, `regularThrough_iff`;
`DatumLemmas.datum_lemmas` — `isSobolevDatum_add` (`:296`), `isSobolevPath_add`
(`:309`), `memForceR_add_compact` (`:348`), `memForceR_of_compact_difference`
(`:381`); `InsertionFamilyAPI` — the assembled family (`blowup`,
`velocity_smooth`, `momentum`, `initial`, `incompressible`,
`velocityDifference_support`, `forceDifference_compact`, `force_formula`,
`reference`, …).

What the **assembly** (`Section4/R42/Assembly.lean` + `Bindings/InsertionFamily.lean`)
already proves for `u_ε = v + w_ε + U_ε`, `p_ε = π + P_ε`, `g_ε = g + H_ε + F_ε`:
`momentum` on `Ioo 0 T`, `incompressible` on `Ico 0 T`, `velocity_smooth`/
`pressure_smooth` on `Ico 0 T ×ˢ univ`, `initial` (`u_ε(·,0)=a`), the localization
`velocityDifference_support ⊆ ball x₀ r`, `forceDifference_compact`
(`g_ε - g ∈ C_c^∞`), and the pointwise `blowup : SpeedUnboundedAt T u_ε`.
What it does **not** discharge: `ClassicalSolutionR.sobolev` and
`.pressure_gradient` for `u_ε`/`p_ε`.

---

## Sub-lemma table

| # | statement (Lean-ready, informal `∀`) | size | blocker |
|---|---|---|---|
| **1** `sol_on_shorter` | `∀ ε ∈ Ioc 0 ε₀, ∀ S, 0 < S → S < family.T → ∃ w : Data.ClassicalSolutionR ν family.a (family.force ε) S, w.velocity = family.velocity ε ∧ w.pressure = family.pressure ε` | **M** | `sobolev` field for `u_ε` (1e-i time-continuity, M) + `pressure_gradient` (1f, M) |
| **2** `blowup_essSup` | `∀ ε ∈ Ioc 0 ε₀, MaximalPartial.limsupLeft family.T (fun t => MaximalPartial.speedENorm (fun x => family.velocity ε (t,x))) = ⊤` | **M** | pointwise `SpeedUnboundedAt` ⟹ essSup lower bound via continuity (2a); rest S (proved) |
| **3** `memForceR_gε` | `∀ ε ∈ Ioc 0 ε₀, Data.MemForceR (family.force ε)` given `hg : Data.MemForceR family.g` | **S ✅** | **proved** (`memForceR_insertedForce`); only residual is `hg` (R42-V2 field, item d) |
| **4** `upper` | `∀ ε ∈ Ioc 0 ε₀, Data.maximalLifespanR ν family.a (family.force ε) ≤ ENNReal.ofReal family.T` | **S** | none once 1,2,+`a∈X_R` (4a) hold — pure `A02.lifespan_le_of_unbounded` (`hg_ε` now from #3) |
| **5** `lower` | `∀ ε ∈ Ioc 0 ε₀, ENNReal.ofReal family.T ≤ Data.maximalLifespanR ν family.a (family.force ε)` | **S** | none once 1 holds — pure `A02.lifespan_ge_of_forall_shorter` |
| **6** `reference` | `ENNReal.ofReal (family.T + family.margin) < Data.maximalLifespanR ν family.a family.g` | **S ✅** (given paper hyp) | **proved** (`lt_maximalLifespanR_of_regularThrough`) given `RegularThrough ν a g (T+δ)`; residual = R42-V2 carries that hypothesis (6) |

`lifespan` field = `4 ∧ 5` glued by `le_antisymm`.  `referenceLifespan` field = `6`.

---

## (a) Upper bound  `maximalLifespanR ν a g_ε ≤ ofReal T`  (#4, S)

Apply
```
MaximalPartial.lifespan_le_of_unbounded ν a g_ε family.T hν ha hg_ε hT
  (family.velocity ε) (family.pressure ε) sol_on_shorter blowup_essSup
```
(`MaximalPartial.lean`, `lifespan_le_of_unbounded`).  Its arguments:

* `hT : 0 < family.T` — `PacketAPI`/`CorrectionAPI` positivity (S).
* **4a** `ha : a ∈ Data.initialClassR` = `MemHInfty a ∧ IsSolenoidal a`.  From the
  reference: `a = reference.velocity(0,·)` (`InsertionFamilyAPI.initial` /
  `reference.initial`); `ContDiff` of the slice via
  `NavierStokes.SpatialCurl.contDiff_spatialSlice reference.velocity_smooth`;
  the datum at each order from `reference.sobolev` at `t = 0`; `IsSolenoidal`
  from `reference.divergence` at `t = 0`.  Size **S/M**.
* **1** `sol_on_shorter` (below).
* **2** `blowup_essSup` (below).
* **3** `hg_ε : MemForceR g_ε` — **available** via `memForceR_insertedForce`
  (Lifespan.lean, ⇐ `D01.memForceR_of_compact_difference`), given `hg`.

Once 1, 2 and 4a are in hand, #4 is a one-line application.  **S.**

## (b) Lower bound  `ofReal T ≤ maximalLifespanR ν a g_ε`  (#5, S)

Apply
```
MaximalPartial.lifespan_ge_of_forall_shorter ν a g_ε family.T hT
  (fun b hb0 hbT => ⟨(sol_on_shorter ε … b hb0 hbT).choose⟩)
```
Only input is **1** `sol_on_shorter`.  **S** once 1 holds.  N.B. even this
"easy" half is blocked on the `sobolev` field of `u_ε` — `maximalLifespanR` is a
`⨆` over `Nonempty (ClassicalSolutionR …)`, so it needs an *inhabitant*.

## (#1) `sol_on_shorter` — the shared `ClassicalSolutionR ν a g_ε S` (M)

For `0 < S < family.T`, build `w : Data.ClassicalSolutionR ν a g_ε S` with
`w.velocity = u_ε`, `w.pressure = p_ε`.  Fields:

* `horizon_pos`, `velocity_smooth`, `pressure_smooth`, `initial`, `divergence`,
  `momentum` — from the assembly, restricted `Ico 0 S ⊆ Ico 0 family.T`,
  `Ioo 0 S ⊆ Ioo 0 family.T`.  **S** (guard shuffling).
* **1a** `sobolev : ∀ m, ∃ G, ContinuousOn G (Ico 0 S) ∧ ∀ t ∈ Ico 0 S, IsSobolevDatum m (u_ε(t,·)) (G t)`.
  Decompose `u_ε(t,·) = v(t,·) + (w_ε + U_ε)(t,·)`:
  - **1b** the correction slice `d(t,·) := (u_ε - v)(t,·)` has **compact spatial
    support**: `InsertionFamilyAPI.velocityDifference_support` gives
    `tsupport (d(t,·)) ⊆ Metric.ball x₀ r`; **proved** as
    `R42.hasCompactSupport_of_tsupport_subset_ball`. **S ✅**
  - **1c** the correction slice is smooth ⟹ **datum at each order and time**:
    **proved** as `R42.exists_isSobolevDatum_of_contDiff_hasCompactSupport`
    (via D01 `exists_isSobolevDatum_of_contDiff_memLp`). **S ✅**
  - **1d** `reference.sobolev` gives the datum path `G_v` of `v`. **exists ✅**
  - **1e-ii** *(additivity — DONE, registered; review finding 1)*
    `D01.isSobolevDatum_add` (`ForceClass.lean:261`, registered
    `DatumLemmas.lean:296`; side condition `SchwartzPairable`, discharged for a
    continuous field with an order-`0` datum by `schwartzPairable_of_isSobolevDatum`,
    `ForceClass.lean:250`) and `D01.isSobolevPath_add` (`ForceClass.lean:320`,
    registered `:309`) combine `G_v` with the correction datum path; continuity of
    the *sum* path is `ContinuousOn.add`.  **not a blocker.**
  - **1e-i** *(the only real residual, M)* **time-continuity** of the correction
    datum path on `Ico 0 S`.  Machinery (review finding 3): `d = u_ε − v` is
    `ContDiffOn ℝ ∞` on `Ico 0 T ×ˢ univ`, spatially `tsupport ⊆ ball x₀ r` at
    each `t < T`, and `= 0` for `t ≤ T − 2ε²` (`InsertionFamilyAPI.history`).  For a
    fixed `S < T`, multiply by a time cutoff supported in `[0,(S+T)/2]`, `= 1` on
    `[0,S]`; the product is globally `ContDiff` with **compact spacetime support in
    `t > 0`** (= `D01.MemForceCompact`).  Then `D01.contDiff_angularPath`
    (`ForceClass.lean:133`) gives an order-`m` datum path that is `ContDiff ℝ ∞`
    **in time**, agreeing with `d`'s datum on `Ico 0 S` by `isSobolevDatum_unique`
    (`ForceClass.lean:286`).  Residual: the cutoff/extension bookkeeping and the
    `Ico 0 S` vs `Ici 0` domain shuffle.  **M** — an R42-assisted-by-D01 item, **not**
    a missing D01 unit.
* **1f** `pressure_gradient : ∀ t ∈ Ico 0 S, MemLp (pressureGradient p_ε t ·) 2 volume`.
  `p_ε = π + P_ε`; `∇P_ε` has compact spatial support (`pressureDifference_support`)
  ⟹ `L²`; `∇π = ∇(reference.pressure)` is `reference.pressure_gradient`.  Needs a
  gradient-slice additivity in `L²`.  **M.**

## (#2) `blowup_essSup` (M)

Need `limsupLeft T (fun t => speedENorm (u_ε(t,·))) = ⊤`, where
`speedENorm z = eLpNorm z ⊤ volume` and `limsupLeft T φ = Filter.limsup φ (𝓝[<] T)`.

Route from the assembly's `blowup : SpeedUnboundedAt family.T u_ε` (pointwise) +
`velocity_smooth` (slice continuity):

* **2a** *(residual M)* pointwise `∃ x, M < ‖u_ε(t,x)‖` + continuity of `u_ε(t,·)`
  ⟹ `ENNReal.ofReal M ≤ speedENorm (u_ε(t,·))`: `{y : M < ‖u_ε(t,y)‖}` is open
  (continuity) and nonempty, hence positive Lebesgue measure
  (`volume` is `IsOpenPosMeasure`), so `essSup ‖u_ε(t,·)‖ ≥ M`.  Then the
  `frequently`-characterization of `Filter.limsup … = ⊤` closes it.  **M.**
* alternatively via the **rescaled packet** essSup blow-up
  (`ScalingAPI.scaledBlowup`, in essSup form) + boundedness of `v + w_ε`, using
  the **proved** transfer `R42.limsup_eLpNormTop_add_eq_top`:
  `limsup ‖U‖_∞ = ⊤ ∧ ‖w‖ ≤ C ⟹ limsup ‖U + w‖_∞ = ⊤`, whose core is the abstract
  `R42.limsup_eq_top_of_le_add_const` and whose triangle input is
  `R42.eLpNormTop_le_add` / `R42.eLpNormTop_le_ofReal`.  **S ✅** — but this route
  still needs (2a) to put the *packet* blow-up in essSup form first, and a uniform
  bound on `v + w_ε` near `T` (v-boundedness on the compact slab, M).  The direct
  route from `blowup` avoids the v-bound and is preferred.

## (#3) `memForceR_gε` — S ✅ (proved; review finding 2)

`g_ε = g + (H_ε + F_ε)`; `H_ε + F_ε = g_ε - g ∈ C_c^∞`
(`InsertionFamilyAPI.forceDifference_compact : Data.MemForceCompact`, `:272`).
**Proved** as `R42.memForceR_insertedForce` (Lifespan.lean), a single application of
the **registered** D01 unit `D01.memForceR_of_compact_difference`
(`ForceClass.lean:401`, registered `DatumLemmas.lean:381`):
```
memForceR_of_compact_difference : MemForceR g → MemForceCompact (fun z => gε z - g z) → MemForceR gε
```
whose second argument is literally `forceDifference_compact ε hε`.  The only
residual is the **hypothesis** `hg : MemForceR g`: `InsertionFamilyAPI` carries no
such field (`g_ε - g ∈ C_c^∞` alone cannot give `g_ε ∈ F_R`), so an R42-V2 asserting
`memF` must add it (`ATTEMPTS.md §5b item 2`).  Knock-on: `hg_ε` in **#4** is no
longer blocked.

## (#4/#5) glue

`lifespan` field `= le_antisymm (upper …) (lower …)`.  **S** once 1,2 hold.

## (#6) reference clause  `ofReal (T+δ) < maximalLifespanR ν a g`  (S ✅ given paper hyp; review finding 4)

`InsertionFamilyAPI.reference : Data.ClassicalSolutionR ν a g (T+δ)`, `δ = margin > 0`.

* **non-strict** `ofReal (T+δ) ≤ maximalLifespanR ν a g`: immediate from
  `Nonempty (reference)` via `le_iSup₂` on the `⨆`.  **S.**
* **strict `<`, the resolution the split now uses** (was missing): the manuscript's
  hypothesis is "(v,π,g) … **regular through `T+δ`**" (`02-preliminaries.tex:34-36`,
  `04-whole-space.tex:32`) = `Data.RegularThrough ν a g (T+δ)` (a solution on
  `[0, T+δ+δ')`).  Then **`A02.regularThrough_iff` at `T' = T+δ`** gives the field
  verbatim in one step — **no margin identification**, `family.margin` untouched.
  **Proved** as `R42.lt_maximalLifespanR_of_regularThrough` (Lifespan.lean).  The
  only residual is contract-shape: `InsertionFamilyAPI.reference` was **weakened** to
  the half-open `[0,T+δ)` (`Data.ClassicalSolutionR`, giving only `≤`), against
  `research/section4/STATEMENTS.md:332`'s `Icc 0 (T+δ)`; a correct-strength R42-V2
  must carry `RegularThrough ν a g (T+δ)` (equivalently strengthen `reference` to a
  solution past `T+δ`, or read it on `Icc 0 (T+δ)`).  The strengthening is **free**
  downstream: `CorrectionAPI` uses the reference only on the open `(0,T+δ)`
  (`Correction.lean:546-550`), and `InsertionFamilyAPI.reference` is recovered by
  `A02.restrict`.  **S** for the math; the residual is a V2 contract shape.
* the earlier "option (i)" — take `family.margin := δ_A` from `A02.referenceLifespan`
  — is **not available as stated**: `margin = A.scaling.correction.δ` is a projection
  of a `ScalingAPI` that `insertionFamilyStatement` (`InsertionFamily.lean:390-395`)
  receives as a **universally quantified input**, so R42 cannot choose it.  It becomes
  available only via a real re-plumbing (quantify over the reference first, derive
  `δ_A`, then instantiate `correctionStatement` — which does take `δ` as an input,
  `Correction.lean:543` — at `δ_A`).  Recorded for completeness; the
  `regularThrough_iff` route above is the clean one.

---

## Where `hg : MemForceR g` enters (item d)

Only through **#3** → the `MemForceR (family.force ε)` argument of
`MaximalPartial.lifespan_le_of_unbounded` in **#4**.  `InsertionFamilyAPI` carries
**no** hypothesis that the reference force is in `F_R`; `g_ε - g ∈ C_c^∞` alone
cannot give `g_ε ∈ F_R`.  So inhabiting `InsertionLifespanAPI` (or an R42-V2 that
adds `memF`) **must** assume `hg : Data.MemForceR family.g`.  It does **not** enter
#5 or the non-strict half of #6.

## Proved now (S), in `Section4/R42/Lifespan.lean`

`limsup_eq_top_of_le_add_const`, `eLpNormTop_le_ofReal`, `eLpNormTop_le_add`,
`limsup_eLpNormTop_add_eq_top`, `hasCompactSupport_of_tsupport_subset_ball`,
`exists_isSobolevDatum_of_contDiff_hasCompactSupport`, **`memForceR_insertedForce`**
(#3), **`lt_maximalLifespanR_of_regularThrough`** (#6 strict half).  All
standard-3-axioms (`research/R42/axioms_lifespan.lean`).

## Residual (M) — for the assembly lane, not this split

* **1e-i** (M): time-continuity of the correction's datum path via
  `D01.contDiff_angularPath` after a time cutoff + `isSobolevDatum_unique`; the
  additivity (1e-ii) and `ContinuousOn.add` are already registered.
* **1f** (M): `pressure_gradient` for `p_ε = π + P_ε`.
* **2a** (M): pointwise ⟹ essSup lower bound via `IsOpenPosMeasure`.
* **#6 residual** (contract shape): an R42-V2 must carry `RegularThrough ν a g (T+δ)`
  (or a closed-`Icc`/strengthened `reference`); the math is then the one-line
  `lt_maximalLifespanR_of_regularThrough`.
* **hg** (item d): an R42-V2 asserting `memF` must add `hg : MemForceR g`.
