import Contracts.V1.Data

/-!
# R44 specification (draft A): Proposition 4.4, `prop:Rcritical2`

**Regularity on a prescribed finite interval — the `L²_t H^{-1/2}` critical
force at zero initial velocity.**

Statement `paper/sections/04-whole-space.tex:136-143`; proof `:145-174`.
Graph node `R44 ← A04, A05, C01` (`formalization/blueprint/DEPENDENCY_GRAPH.md`,
same three children as R43); transitively `← A02` through A04's continuation
clause; consumer `R44 → R41` (Theorem 4.1), used **only** at `S = T`
(`04-whole-space.tex:179`).  Ledger: `research/section4/STATEMENTS.md` §4
(`:556-660`); R41's consumption `:133-140`.

This file is a **specification**.  It contains one `structure` and no proof with
mathematical content: it assumes nothing, and introduces no `axiom`, no `sorry`,
no `native_decide` and no abstract `Prop` placeholder field.  Both propositional
fields are fully spelled-out statements about named `Contracts.V1.Data` objects,
each written so that a wrong implementation could not satisfy it.

R44 is the `q = 2` twin of Proposition 4.3 (`prop:Rcritical1`, task R43); this
draft deliberately reuses the reconciled R43 shape (`research/R43/Spec.lean`):
`ℝ≥0∞` fail-safe norms, the universal constant(s) as fields quantified before
`ν, S, f`, the conclusion as a strict lifespan inequality against
`maximalLifespanR`, and the `Data`-level force norm rather than any pointwise
Fourier norm.

## The statement (`04-whole-space.tex:136-143`)

> For each `ν, S > 0` there is `r_{ν,S} > 0` such that
> `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2}(ℝ³))} < r_{ν,S}  ⟹  T^ν_{max,ℝ}(0,f) > S`.
> One can take `r_{ν,S} = c ν^{3/2} e^{−C ν S}` for suitable universal positive
> constants `c, C`.

Quantifier order (`STATEMENTS.md:566-569`), transcribed exactly:

    ∃ c, C > 0, ∀ ν, S > 0, ∀ f ∈ 𝓕_ℝ,
        (‖f‖_{L²(0,∞;H^{-1/2})} < c ν^{3/2} e^{−C ν S}  ⟹  T^ν_{max,ℝ}(0,f) > S).

Three faithfulness points the paper is explicit about, each load-bearing here:

* **Initial velocity is exactly zero** (`04-whole-space.tex:139`, and risk note
  `STATEMENTS.md:634-637`, "`a = 0` is essential"): Grönwall starts from
  `Y(0) = 0`.  A general-`a` version would carry a `Y(0)²e^{C₂νS}` term and the
  radius would then depend on `a`.  The datum is spelled `(fun _ => 0)`, exactly
  as `Data.breakdownSetRZero` (`Data.lean:686`) unfolds it, so the R41
  consequence below needs no conversion to reach `B^ℝ_{ν,0,T}`.  Because the
  datum is zero there is **no spatial homogeneous norm** in this contract, unlike
  R43 (which carried `‖a‖_{Ḣ^{1/2}}` and a local `dotHomogeneousENorm`).

* **The force norm is inhomogeneous `H^{-1/2}`, integrated in `L²` over
  `(0,∞)`** (`04-whole-space.tex:140`).  The paper flags at `:173` that this is
  essential: "The inhomogeneous norm is essential here because smallness in
  `H^{-1/2}` does not control the homogeneous negative norm at low frequencies."
  Formalising the hypothesis with `Ḣ^{-1/2}` (i.e. `forceHomogeneousENorm`)
  would make the statement **false as proved** — a generic `f ∈ 𝓕_ℝ` can have an
  infinite homogeneous negative norm at low frequencies (compare
  `04-whole-space.tex:78`).  So the norm used is
  `Data.forceSobolevENormL2 (-1/2) f = ‖f‖_{L²(0,∞;H^{-1/2})}`
  (`Data.lean:235`, `= forceSobolevENorm 2 (-1/2) f`), the measurable-datum-path
  Bochner `H^{-1/2}` norm over `forceTimeMeasure = (0,∞)`, and **not**
  `forceHomogeneousENorm 2 (-1/2)`.  This is the R43-gap-G3 trap turned into a
  correct choice: R43's `COMPARISON.md` §4 warns the homogeneous negative norm
  can be `⊤`; here the paper's own remedy is the inhomogeneous norm.

* **The conclusion is `T^ν_{max,ℝ}(0,f) > S`, a strict lifespan inequality up to
  the finite horizon `S`** (`04-whole-space.tex:141`), not global regularity
  (contrast R43's `= ⊤`) and not `RegularThrough`.  Transcribed as
  `ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f`.  This is the paper's
  literal statement, and it is exactly what A04 produces: `extendsBeyond`
  (`research/A04/Spec.lean:613`) concludes `ENNReal.ofReal S < maximalLifespanR
  ν a f`.  It is provably equivalent to `RegularThrough ν (fun _ => 0) f S`
  (`Data.lean:664`): `ofReal S < ⨆_{S'} ⨆_{Nonempty (Sol S')} ofReal S'` holds
  iff some horizon `S' > S` carries a solution, i.e. iff `∃ δ > 0` with a
  solution on `[0, S+δ)`.  The lifespan form is chosen because it is the shape
  the paper writes and the shape A04 hands over.

## Fail-safe discipline and the finiteness gap R44 needs from D01

Every norm is `ℝ≥0∞`-valued and none is routed through `.toReal`, so a missing
datum path fails safe to `⊤`, the smallness hypothesis
`_ < ENNReal.ofReal (radius ν S)` then fails (a finite positive bound is never
exceeded by `⊤`), and the statement is never satisfied by accident.

That fail-safety makes the **statement** well-formed with no extra hypothesis.
It does **not** by itself make the contract *useful*, and this is the negative-
order analogue of R43's gap **G3** (`research/R43/COMPARISON.md` §4).  `MemForceR`
(`Data.lean:544`) supplies strongly-measurable finite Bochner datum paths only
at **integer** orders `m : ℕ`; the norm here is at order `-1/2`, which is not an
integer.  So on the current definitions `forceSobolevENormL2 (-1/2) f` could a
priori be `⊤` for a genuine `f ∈ 𝓕_ℝ`.  Two consequences:

* `R41`'s use is still sound without any new lemma: the ball
  `{f ∈ 𝓕_ℝ : ‖f‖_{L²_tH^{-1/2}} < radius ν T}` contains `f = 0`
  (`forceSobolevENormL2 (-1/2) (fun _ => 0) = 0`, the zero datum path is finite
  and measurable), so it is a nonempty relative neighbourhood of `0`; and every
  `f` it contains has finite norm `< radius`, so `main`/`nonDensityBallZero`
  apply to all of them.  A norm-`⊤` force is simply not in the ball.

* But for the paper's phrase "the relative `L²(0,∞;H^{-1/2})` topology on `𝓕_ℝ`"
  (`04-whole-space.tex:8`) to be faithful — for `𝓕_ℝ` to sit inside the normed
  space at all — R44 needs from **D01** the finiteness lemma

      ∀ f, MemForceR f → forceSobolevENormL2 (-1/2) f ≠ ⊤.

  This is easier than R43's G3: `-1/2 < 0`, so it follows from the `m = 0`
  integer path of `MemForceR` (`H⁰ = L²`, `MemLp G 2 forceTimeMeasure`) together
  with the inhomogeneous index monotonicity `‖·‖_{H^{-1/2}} ≤ ‖·‖_{H⁰}` lifted to
  datum paths, i.e. `forceSobolevENorm 2 (-1/2) f ≤ forceSobolevENorm 2 0 f`.
  Neither piece is currently a registered lemma; both belong in D01
  (`DatumLemmas`).  It is a proof/faithfulness input, not a field of this
  statement.

## The proof route, for the record (owned elsewhere)

`04-whole-space.tex:145-174`.  With `J = (I−Δ)^{1/2}`, `Y = ‖u‖_{H^{1/2}}`,
`Z = ‖∇u‖_{H^{1/2}}`, `B = ‖f‖_{H^{-1/2}}` and the exact weight identity
`‖u‖²_{H^{3/2}} = Y² + Z²`, testing against `Ju` and Fourier Cauchy–Schwarz give
eq:Rcritical2 `(Y²)' + νZ² ≤ C₂νY² + C₃ν^{-1}B²` while `Y ≤ θν`.  Grönwall from
`Y(0) = 0` yields `Y(t)² ≤ C₃ν^{-1}e^{C₂νS}‖f‖²_{L²_tH^{-1/2}}` for `t ≤ S` while
`Y ≤ θν`; choosing `r_{ν,S}` so this is `< θ²ν²/4` makes a first crossing
`Y = θν` contradictory (`:169`, an implicit first-exit-time argument on
`[0, min(S, T_max))`).  Then `‖u‖₃ ≤ CY ≤ Cθν` discharges the `H¹` absorption
eq:RH1, and the `L²` estimate eq:RL2 plus the `∫₀^S‖u‖²_{H²} < ∞` assembly (with
`a = 0`: `K(S) = ∫₀^S‖f‖₂`, `‖∇a‖₂ = 0`) feed A04's continuation to exclude a
maximal lifespan at or before `S`.  None of these quantities is a hypothesis of
the fields below; the manuscript's theorem carries none.  They are owned by:

* **A05** — `‖u‖₃ ≤ C(1/2)‖u‖_{Ḣ^{1/2}}`, `‖∇u‖₆ ≤ C‖Δu‖₂`
  (`research/A05/Spec.lean:366,396`) and the homogeneous-to-inhomogeneous
  comparison `homogeneousLeSobolev` (`:268`) needed because `Y, Z` are the
  **inhomogeneous** norms;
* **C01** — eq:RL2 `l2Bound` (`research/C01/Spec.lean:383`) and the
  `∫₀^S‖u‖²_{H²}` assembly at zero datum `h2TimeIntegralZeroDatum` (`:599`),
  gated by `C₁‖u‖₃ ≤ ν/4`;
* **A04** — the continuation adapter `extendsBeyond` at the prescribed `S`
  (`research/A04/Spec.lean:613`), which is what turns the finite `∫₀^S‖u‖²_{H²}`
  into `ENNReal.ofReal S < maximalLifespanR ν a f`;
* **A02** — the maximal-solution family behind `maximalLifespanR`.

The proof's internal constants `θ, C₀, C₂, C₃` and the shrinkings ("Take `θ`
smaller if necessary", `:171`) are **not** exposed as fields: they belong to the
Grönwall/absorption bookkeeping that produces the two universal constants `c, C`
of the radius, and `STATEMENTS.md:657-660` records that `C₂, C₃` are not even
pinned by the paper's outline.  The contract offers only `c, C`.
-/

noncomputable section

namespace BlowupDensity.R44.DraftA

open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- **Proposition 4.4** (`prop:Rcritical2`, "Regularity on a prescribed finite
interval"), `paper/sections/04-whole-space.tex:136-143`, in the shape
`research/section4/STATEMENTS.md:572-583` fixes and `R41` consumes at `S = T`.

The universal constants `c` and `C` are **fields**, hence quantified before every
`ν`, `S` and `f`, as `04-whole-space.tex:143` requires ("for suitable universal
positive constants `c, C`") and as the `r_{ν,T}`-ball scaling of Theorem 4.1(ii)
needs (`STATEMENTS.md:566-569`).  Both are strictly positive; the radius depends
on both `ν` and `S` (`04-whole-space.tex:143,173`, "The radius depends on `S`"),
but on **no** `f`. -/
structure RCritical2API where
  /-- `04-whole-space.tex:143`, "universal positive constants `c, C`": the leading
  coefficient of the smallness radius, in units of `ν^{3/2}`.  A single real,
  `ν`- and `S`-free. -/
  c : ℝ
  /-- `04-whole-space.tex:143`: the exponential rate constant `C` in
  `e^{−C ν S}`.  A single real, `ν`- and `S`-free; it is what makes the radius
  shrink as `νS` grows (`:16`, "a regular neighborhood whose radius depends on
  `T`"). -/
  C : ℝ
  /-- `04-whole-space.tex:143`, "`c > 0`".  Load-bearing: without it `c ≤ 0` makes
  `radius ν S ≤ 0`, so `ENNReal.ofReal (radius ν S) = 0`, the smallness
  hypotheses become unsatisfiable, and the structure would be inhabited by a
  content-free statement. -/
  hc : 0 < c
  /-- `04-whole-space.tex:143`, "`C > 0`".  Positivity of the rate; with it the
  radius is a genuine decreasing exponential rather than a growing one. -/
  hC : 0 < C
  /-- The smallness radius `r_{ν,S}` of `04-whole-space.tex:137`, kept as a field
  (rather than inlined) so that `RMainAPI.nonDensityZero` can consume `radius ν T`
  without re-deriving `c, C` (`STATEMENTS.md:585-586`).  Real-valued; it enters
  the `ℝ≥0∞` hypotheses below through `ENNReal.ofReal`. -/
  radius : ℝ → ℝ → ℝ
  /-- `04-whole-space.tex:143`: `r_{ν,S} = c ν^{3/2} e^{−C ν S}`, transcribed with
  `Real.rpow` for the `3/2` power and `Real.exp` for the exponential.  Pinning the
  formula (rather than leaving `radius` opaque) records the exact `ν`- and
  `S`-dependence the paper states. -/
  radiusFormula : ∀ ν S : ℝ,
    radius ν S = c * ν ^ ((3 : ℝ) / 2) * Real.exp (-(C * ν * S))
  /-- The radius is strictly positive for every `ν, S > 0`, so
  `ENNReal.ofReal (radius ν S)` is a positive finite threshold and the ball
  `{f : ‖f‖ < radius ν S}` is a genuine neighbourhood of `0`.  Immediate from
  `radiusFormula`, `hc`, and `ν^{3/2}, e^{…} > 0`; carried as a field so consumers
  need not re-derive it. -/
  radiusPos : ∀ ν S : ℝ, 0 < ν → 0 < S → 0 < radius ν S
  /-- **The theorem** (`04-whole-space.tex:137-143`):

    `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2})} < r_{ν,S}  ⟹  T^ν_{max,ℝ}(0,f) > S`,

  for every `ν > 0` and every `S > 0`.

  * `f` ranges over `MemForceR` (`Data.lean:544`), the manuscript's `𝓕_ℝ`.
  * The initial velocity is `(fun _ => 0)` — exactly zero
    (`04-whole-space.tex:139`); this datum is not quantified.
  * `forceSobolevENormL2 (-1/2) f` (`Data.lean:235`) is
    `‖f‖_{L²(0,∞;H^{-1/2})}`, the **inhomogeneous** `H^{-1/2}` norm over
    `(0,∞)` — **not** `forceHomogeneousENorm 2 (-1/2)`, which the paper says at
    `:173` fails to control the force; see the module docstring.
  * The threshold `ENNReal.ofReal (radius ν S)` is positive and finite
    (`radiusPos`), so an `f` whose critical norm is `⊤` fails the hypothesis
    rather than meeting it.
  * `ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f` (`Data.lean:657`) is
    `T^ν_{max,ℝ}(0,f) > S`: the maximal lifespan strictly exceeds the finite
    horizon `S`.  No implementation can satisfy this with a solution that breaks
    down at or before `S`. -/
  main :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1/2 : ℝ) f < ENNReal.ofReal (radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f
  /-- **The single consequence `R41` consumes** (`STATEMENTS.md:133-140`,
  `04-whole-space.tex:179`, "For `q = 2`, use Proposition 4.4 with `S = T`"),
  the `S = T` instance packaged as disjointness from the breakdown set:

    `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2})} < r_{ν,T}  ⟹  f ∉ B^ℝ_{ν,0,T}`,

  for every `ν > 0` and every `T > 0`.  `breakdownSetRZero ν T` (`Data.lean:686`)
  is `B^ℝ_{ν,0,T} = {f ∈ 𝓕_ℝ : T^ν_{max,ℝ}(0,f) ≤ T}`, so this says the ball of
  radius `r_{ν,T}` about `0` in the `L²_tH^{-1/2}` metric "contains no element of
  `B^ℝ_{ν,0,T}`", which is exactly the ledger's phrasing.  Combined with
  `‖·‖_{H^{-1/2}} ≤ ‖·‖_{H^s}` for `s ≥ −1/2`, `RMainAPI.nonDensityZero` turns
  this into a nonempty relative open ball missing `B^ℝ_{ν,0,T}` in the
  `L²_tH^s` metric for every `s ≥ −1/2` (`STATEMENTS.md:138-140`).

  Kept as its own field, rather than left to be derived from `main`, on the same
  ground R43 keeps `inhomogeneousAtZero` (`research/R43/Spec.lean`,
  `STATEMENTS.md:522`): so that `R41` performs no reduction.  The reduction it
  saves is the `S := T` instantiation of `main` followed by the contradiction
  `T^ν_{max}(0,f) > T` versus `T^ν_{max}(0,f) ≤ T` inside `breakdownSetRZero`. -/
  nonDensityBallZero :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1/2 : ℝ) f < ENNReal.ofReal (radius ν T) →
          f ∉ breakdownSetRZero ν T

end BlowupDensity.R44.DraftA
