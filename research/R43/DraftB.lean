import Contracts.V1.Data

/-!
# R43 draft specification (draft B): global regularity for small critical data and `L¹` force

Task `collaboration/tasks/R43.md`, graph node `R43` in
`formalization/blueprint/DEPENDENCY_GRAPH.md` (`R43 ← A04, A05, C01`; consumer
`R43 → R41`).  Statement: Proposition 4.3, `prop:Rcritical1`,
`paper/sections/04-whole-space.tex:82-89`; proof `:90-133`.

This file is a **specification draft only**.  It contains two `def`s and one
`structure`.  It proves nothing with mathematical content, assumes nothing, and
introduces no `axiom`, no `sorry` and no abstract `Prop` placeholder field:
every propositional field is a fully spelled-out statement about explicitly
named objects.

## What Proposition 4.3 says (`04-whole-space.tex:82-89`)

> There is a universal `c > 0` such that, for `a ∈ 𝒳_ℝ` and `f ∈ 𝓕_ℝ`,
> `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹_t Ḣ^{1/2}_x} < cν  ⟹  T^ν_{max,ℝ}(a,f) = ∞`.
> In particular, for `a = 0`, the ball `‖f‖_{L¹_t H^{1/2}} < cν` consists of
> globally regular inputs.

The quantifier order is decisive and is transcribed exactly
(`research/section4/STATEMENTS.md:434-437`):

    ∃ c > 0, ∀ ν > 0, ∀ a ∈ 𝒳_ℝ, ∀ f ∈ 𝓕_ℝ, (smallness ⟹ T_max = ∞).

* `c` is a **single universal real**, chosen before every `ν`, `a` and `f`.  It
  is a field of the structure, hence bound outside all the `∀`s of the two
  conclusion clauses; a formalisation that let `c` depend on `ν` would still be
  true but would break the `cν`-ball scaling Theorem 4.1's converse needs
  (`research/section4/STATEMENTS.md:521-524`).  The two proof shrinkings
  `c < 1/(4C₀)` (`04-whole-space.tex:102`) and `C₁‖u‖₃ ≤ ν/4` (`:112`) are both
  `ν`-free because `y ≤ cν`, so a single `c` suffices; `C₀`, `C₁` are the
  proof's *internal* constants and are not exposed by the contract, which offers
  only `c`.
* `a` is **quantified**, not fixed and not zero (contrast Proposition 4.4).  The
  time domain of the force norm is `(0,∞)`.  The conclusion is **global**
  regularity `T_max = ∞`, i.e. `maximalLifespanR ν a f = ⊤`, not regularity up
  to a horizon.

## The two fields, and why both

* `universal` is the theorem itself, over general `a ∈ 𝒳_ℝ`.
* `inhomogeneousAtZero` is the "in particular" clause with `a = 0` and the
  **inhomogeneous** `H^{1/2}` force norm.  It is the **single consequence R41
  consumes** (`research/section4/STATEMENTS.md:128-133`): "there is a universal
  `c > 0` such that `{f ∈ 𝓕_ℝ : ‖f‖_{L¹_t H^{1/2}} < cν}` contains no element of
  `B^ℝ_{ν,0,T}` (because each such `f` has `T^ν_{max,ℝ}(0,f) = ∞ > T`)".  It is
  logically derivable from `universal` (put `a = 0`; `‖0‖_{Ḣ^{1/2}} = 0`,
  `0 ∈ 𝒳_ℝ`, and `‖f‖_{L¹_t Ḣ^{1/2}} ≤ ‖f‖_{L¹_t H^{1/2}}` from
  `04-whole-space.tex:132`), but it is kept as its own field, with the **same**
  `c`, because that is the shape `RMainAPI.nonDensityZero` consumes at `q = 1`
  (`research/section4/STATEMENTS.md:509`, `:132-133`) and a consumer should not
  have to redo the reduction.

## What the proof consumes (documented in `COMPARISON_B.md`, not restated here)

`R43 ← A04, A05, C01`, and transitively A02 through A04's continuation clause.
The proof (`04-whole-space.tex:90-133`) tests the projected equation against
`Λu` to get its own `eq:Rcritical1` and the propagation `y(t) ≤ y(0) + ∫₀ᵗ b`
on `{y ≤ ν/(2C₀)}` (both **R43-owned**, `04-whole-space.tex:96-104`; C01's
docstring is explicit that `eq:Rcritical1` is not C01's), then consumes:

* **A05** `CriticalEmbeddingAPI` — `‖u‖₃ ≤ Cy`, `‖∇u‖₃ + ‖Λu‖₃ ≤ Cz`,
  `‖∇u‖₆ ≤ C‖Δu‖₂` (`velocityCriticalL3`, `derivativeCriticalL3`,
  `gradientLSix`);
* **C01** `EnergyAbsorptionAPI` — `eq:RL2` (`l2Bound`), `eq:RH1`
  (`enstrophyIntegralBound`), and the assembly `∫₀ˢ ‖u‖²_{H²} < ∞`
  (`h2TimeIntegral`);
* **A04** `ContinuationAPI` — `lifespanInfiniteOfLocallyFinite`: bounded
  `∫₀ˢ ‖u‖²_{H²}` at every finite `S ≤ T_max` forces `T_max = ⊤`;
* **A02** `MaximalSolutionAPI` — `exists_maximal`: the maximal solution family
  `(u,p)` on every `[0,S)` below `T_max`, the input A04's clause needs.

None of these is restated as a field of the R43 structure: the *statement* of
Proposition 4.3 is self-contained in the canonical objects of
`Contracts.V1.Data`, and adding the consumed clauses as hypotheses would make
`universal` weaker than the manuscript's own theorem, which carries no such
riders.  The provenance table and the gap analysis (which sibling clauses are
missing) live in `COMPARISON_B.md`, as the task's deliverable 2 asks.

## Conventions

Every object quantified over is the canonical one of
`verification/Contracts/V1/Data.lean` (`research/D01/PAPER_TO_LEAN.md`):
`initialClassR` is `𝒳_ℝ`, `MemForceR` is `𝓕_ℝ`, `maximalLifespanR ν a f` is
`T^ν_{max,ℝ}(a,f)` valued in `[0,∞]` so that global regularity is `⊤`
(`Data.lean:650-658`).  Time is the first spacetime coordinate.

## Why the norms are `ℝ≥0∞`, and which realization

The smallness hypothesis is an inequality in `ℝ≥0∞`, so a datum or force with an
**infinite** critical norm cannot satisfy it vacuously — the fail-safe direction
is `⊤`, never a junk finite value (`Contracts/V1/Data.lean:41-53`,
`REVIEW_B` issue 2).

* `‖f‖_{L¹_t Ḣ^{1/2}}` is `Data.forceHomogeneousENorm 1 (1/2) f`
  (`Data.lean:390`), the honest measurable-datum-path Bochner norm, `⊤` when no
  path exists.
* `‖f‖_{L¹_t H^{1/2}}` (the `inhomogeneousAtZero` clause) is
  `Data.forceSobolevENormL1 (1/2) f` (`Data.lean:231`), likewise honest.
* `‖a‖_{Ḣ^{1/2}}` is `dotHalfSpatialENorm` below, the **datum-infimum** spatial
  homogeneous norm, and deliberately **not** `Data.dotHHalfENorm`
  (`Data.lean:427`).  `Data.dotHHalfENorm` is the literal pointwise Fourier
  integral `homogeneousFourierENorm (1/2)`, whose own docstring
  (`Data.lean:406-409`) forbids its use on a general `H^∞` slice, where it
  silently totalizes to a junk `0`.  A general `a ∈ 𝒳_ℝ` is `H^∞` but need not
  be `L¹`, so `dotHHalfENorm a` could read `0` for a large datum and make
  `universal` a **false** statement (smallness would hold, yet `a` may blow up).
  The honest quantity for `H^∞` fields is the `L²` norm of the order-`1/2`
  homogeneous datum, i.e. `A05.Draft.dotHomogeneousENorm (1/2)`
  (`research/A05/Spec.lean`); `A05` is a `research/` draft and not importable, so
  the identical definition is inlined here and tagged.  For `a ∈ 𝒳_ℝ` this norm
  is finite (`‖a‖_{Ḣ^{1/2}} ≤ ‖a‖_{H^{1/2}} < ∞`,
  `research/section4/STATEMENTS.md:471`), so the hypothesis is a genuine
  smallness and not vacuous.  See `COMPARISON_B.md`: promoting this datum-form
  `Ḣ^s` spatial norm into `Data.lean` (or A05's registered contract) is the one
  D01/A05 gap this statement exposes.
-/

noncomputable section

namespace BlowupDensity.R43.DraftB

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

/-! ## 0. The spatial critical norm `‖·‖_{Ḣ^{1/2}}` in its honest realization -/

/-- `04-whole-space.tex:85` and `appendix-b-embeddings.tex:26-27`,
`‖z‖_{Ḣ^{1/2}}` **for a physical field**: the `L²` norm of the order-`1/2`
homogeneous datum of the tempered vector distribution the field represents, and
`⊤` when the field has no such datum.  The empty infimum in `ℝ≥0∞` is `⊤`, so
this is total and fail-safe.

This is `⟪A05:dotHomogeneousENorm⟫` at `s = 1/2` (`research/A05/Spec.lean`),
reproduced verbatim because `A05` is a `research/` draft and cannot be imported.
It is the datum-infimum over `Data.IsHomogeneousSliceDatum` (`Data.lean:364`),
the same building block A05 uses, and it is **not** `Data.dotHHalfENorm`
(`Data.lean:427`), which is the Fourier-integral form usable only on `L¹ ∩ L²`
slices; see the module docstring for why the distinction is load-bearing for the
truth of `universal`. -/
def dotHalfSpatialENorm (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev (1 / 2 : ℝ) // IsHomogeneousSliceDatum (1 / 2 : ℝ) z G},
    ‖G.1‖ₑ

/-! ## 1. The contract -/

/-- **Proposition 4.3** (`prop:Rcritical1`, "Global regularity for small critical
data and `L¹` force"), `paper/sections/04-whole-space.tex:82-89`.

The universal constant `c` is a field, hence quantified **before** every `ν`,
`a` and `f`, as `04-whole-space.tex:82` requires ("There is a universal
`c > 0` such that …") and as `research/section4/STATEMENTS.md:434-437`,`:483-485`
insist for the `cν`-ball scaling of Theorem 4.1.

This is a specification: every field is either data or a fully spelled-out
manuscript statement; no field is an abstract proposition variable, and the
consumed sibling clauses (A02/A04/A05/C01) are documented in `COMPARISON_B.md`
rather than carried here, so that `universal` states exactly the manuscript's
theorem with no added hypothesis. -/
structure RCritical1API where
  /-- `04-whole-space.tex:82` "There is a universal `c > 0`": the smallness
  radius, in units of `ν`.  A single real, `ν`-free, shared by both conclusion
  clauses. -/
  c : ℝ
  /-- `04-whole-space.tex:82` "`c > 0`". -/
  hc : 0 < c
  /-- **The theorem** (`04-whole-space.tex:83-86`):

    `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹(0,∞;Ḣ^{1/2})} < cν  ⟹  T^ν_{max,ℝ}(a,f) = ∞`,

  for every `ν > 0`, every `a ∈ 𝒳_ℝ` and every `f ∈ 𝓕_ℝ`.

  * The left-hand sum is in `ℝ≥0∞`: `dotHalfSpatialENorm a` is `‖a‖_{Ḣ^{1/2}}`
    in its honest datum realization (see module docstring — not
    `Data.dotHHalfENorm`), and `forceHomogeneousENorm 1 (1/2) f` is
    `‖f‖_{L¹(0,∞;Ḣ^{1/2})}` (`Data.lean:390`).  The threshold `cν` is injected by
    `ENNReal.ofReal`; because `c > 0` and `ν > 0` it is a positive finite bound,
    so a datum or force with an infinite critical norm fails the hypothesis
    rather than meeting it vacuously.
  * The conclusion `maximalLifespanR ν a f = ⊤` (`Data.lean:657`) is global
    regularity, `T^ν_{max,ℝ}(a,f) = ∞`.  `⊤` is the top of `ℝ≥0∞`, unreachable
    by any finite horizon, so a wrong implementation could not satisfy this with
    a finite lifespan.

  *R43's own step, for the record* (`04-whole-space.tex:96-104`): testing the
  projected equation against `Λu` gives `eq:Rcritical1`
  `½(y²)' + (ν − C₀y)z² ≤ by` with `y = ‖u‖_{Ḣ^{1/2}}`, `z = ‖u‖_{Ḣ^{3/2}}`,
  `b = ‖f‖_{Ḣ^{1/2}}`; regularised division and `c < 1/(4C₀)` propagate
  `y(t) ≤ y(0) + ∫₀ᵗ b < cν` through the lifespan; then C01's `eq:RL2`/`eq:RH1`
  and its `H²` assembly, with the absorption `C₁‖u‖₃ ≤ ν/4` reached through
  A05's `‖u‖₃ ≤ Cy`, give `∫₀ˢ ‖u‖²_{H²} < ∞` at every finite `S ≤ T_max`, and
  A04's continuation clause (fed A02's maximal solution) turns that into
  `T_max = ⊤`.  None of these intermediate quantities is a field: the theorem
  carries none of them as a hypothesis. -/
  universal :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHalfSpatialENorm a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (c * ν) →
            maximalLifespanR ν a f = ⊤
  /-- **The "in particular" clause** (`04-whole-space.tex:87-89`), with `a = 0`
  and the inhomogeneous force norm, using the **same** `c`:

    `‖f‖_{L¹(0,∞;H^{1/2})} < cν  ⟹  T^ν_{max,ℝ}(0,f) = ∞`,

  for every `ν > 0` and every `f ∈ 𝓕_ℝ`.  `forceSobolevENormL1 (1/2) f`
  (`Data.lean:231`) is `‖f‖_{L¹(0,∞;H^{1/2})}`; the initial velocity is the zero
  field `fun _ => 0`, which lies in `𝒳_ℝ`.

  This is **the single consequence R41 consumes**
  (`research/section4/STATEMENTS.md:128-133`); it says every such `f` produces
  global regularity, i.e. lies outside every whole-space breakdown set
  `B^ℝ_{ν,0,T}` (`Data.breakdownSetRZero`, `Data.lean:687`), which is what
  `RMainAPI.nonDensityZero` turns into non-density of `B^ℝ_{ν,0,T}` in the
  `L¹_t H^s` metric for every `s ≥ 1/2` (via `‖·‖_{H^{1/2}} ≤ ‖·‖_{H^s}`).

  Derivable from `universal` at `a = 0` (`‖0‖_{Ḣ^{1/2}} = 0`, `0 ∈ 𝒳_ℝ`, and
  `‖f‖_{L¹_t Ḣ^{1/2}} ≤ ‖f‖_{L¹_t H^{1/2}}` from `04-whole-space.tex:132`), but
  kept as its own field so R41 needs no reduction. -/
  inhomogeneousAtZero :
    ∀ ν : ℝ, 0 < ν →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (c * ν) →
          maximalLifespanR ν (fun _ => 0) f = ⊤

end BlowupDensity.R43.DraftB
