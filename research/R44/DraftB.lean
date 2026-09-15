import Contracts.V1.Data

/-!
# R44 specification (draft B): Proposition 4.4, `prop:Rcritical2`

**Regularity on a prescribed finite interval** (the critical `L²`-in-time force,
zero datum).  Statement `paper/sections/04-whole-space.tex:136-144`; proof
`:145-174`.  Graph node `R44 ← A04, A05, C01` (same three children as R43,
different instantiation, `research/section4/STATEMENTS.md:598`), transitively
`← A02` through A04's continuation clause and `← D01` for the data objects;
consumer `R44 → R41` (`STATEMENTS.md:133-136`).  Ledger `STATEMENTS.md` §4
(`:556-651`).

This file is a **specification** written blind (draft B; the reconciliation
against draft A happens later).  It contains one `structure` and no `def`; it
proves nothing with mathematical content, assumes nothing, and introduces no
`axiom`, no `sorry`, no `native_decide` and no abstract `Prop` placeholder
field.  Both propositional fields are fully spelled-out statements about named
`Contracts.V1.Data` objects, so a wrong implementation could not satisfy them.

## The statement (`04-whole-space.tex:136-144`)

> For each `ν, S > 0` there is `r_{ν,S} > 0` such that
> `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2})} < r_{ν,S}  ⟹  T^ν_{max,ℝ}(0,f) > S`.
> One can take `r_{ν,S} = c ν^{3/2} e^{−CνS}` for suitable universal positive
> constants `c, C`.

Quantifier order, transcribed exactly (`STATEMENTS.md:569`):

    ∃ c, C > 0, ∀ ν, S > 0, ∀ f ∈ 𝓕_ℝ,
      (‖f‖_{L²_tH^{-1/2}} < c ν^{3/2} e^{−CνS}  ⟹  T^ν_{max,ℝ}(0,f) > S).

Four load-bearing facts, each of which a careless formalisation gets wrong:

1. **Two universal constants `c, C`, both `ν`- and `S`-free**
   (`04-whole-space.tex:143`, `STATEMENTS.md:594`).  They are **fields**, hence
   quantified before every `ν`, `S`, `f`.  The radius `r_{ν,S}` depends on
   *both* `ν` and `S`; the `S`-dependence is genuine and enters as `e^{−CνS}`,
   so the ball shrinks as `S` grows.  This is exactly why the `q = 2` result is
   *interval* regularity, not the global regularity of Proposition 4.3.

2. **The initial velocity is exactly zero** (`04-whole-space.tex:137,141`,
   risk note `STATEMENTS.md:631`).  Grönwall starts from `Y(0) = 0`; a nonzero
   `a` would carry a `Y(0)² e^{C₂νS}` term and the radius would depend on `a`.
   The datum is spelled `fun _ => 0`, matching `Data.breakdownSetRZero`
   (`Data.lean:686-687`), so `R41` reaches `B^ℝ_{ν,0,T}` with no conversion.

3. **The force norm is INHOMOGENEOUS `H^{-1/2}`, not homogeneous `Ḣ^{-1/2}`**
   (`04-whole-space.tex:140,173`, risk note `STATEMENTS.md:570-571,639-640`).
   The paper states the reason in as many words (`:173`): *"The inhomogeneous
   norm is essential here because smallness in `H^{-1/2}` does not control the
   homogeneous negative norm at low frequencies."*  Formalising the hypothesis
   with a homogeneous `Ḣ^{-1/2}` norm would make the statement **false as
   proved**, and would also route through the finiteness lemma that is still
   open (see the `main` field docstring, "the vacuity trap").  The correct
   object is `Data.forceSobolevENormL2 (-1/2)` = `forceSobolevENorm 2 (-1/2)`
   (`Data.lean:225,235`), the inhomogeneous `L²(0,∞;H^{-1/2})` Bochner norm,
   **not** `Data.forceHomogeneousENorm 2 (-1/2)` (`Data.lean:390`).

4. **The conclusion is the strict lifespan inequality `T^ν_{max,ℝ}(0,f) > S`**
   (`04-whole-space.tex:141`), written `ENNReal.ofReal S < maximalLifespanR ν 0 f`;
   see the `main` docstring for why this and not `RegularThrough`.

## Conventions (every quantified object is `Contracts/V1/Data.lean`'s)

`MemForceR` is `𝓕_ℝ` (`Data.lean:544`, eq:Rclasses `02-preliminaries.tex:17`);
`forceSobolevENormL2 s f` is `‖f‖_{L²(0,∞;H^s(R³))}` (`Data.lean:235`, the
`q = 2` abbreviation of `Data.forceSobolevENorm`);
`maximalLifespanR ν a f` is `T^ν_{max,ℝ}(a,f)` valued in `[0,∞]` with `⊤` for
global regularity (`Data.lean:657`, `02-preliminaries.tex:32`);
`breakdownSetRZero ν T` is `B^ℝ_{ν,0,T} = {f ∈ 𝓕_ℝ : T^ν_{max,ℝ}(0,f) ≤ T}`
(`Data.lean:686`, eq:Rsingularforces `02-preliminaries.tex:42`).  Time is the
first spacetime coordinate; the force time norm runs over `(0,∞)`.

**Every force norm is `ℝ≥0∞`-valued and never routed through `.toReal`**, so a
force with no measurable `H^{-1/2}` datum path fails safe to `⊤`, the smallness
hypothesis then fails, and the statement is never satisfied by accident.  The
threshold `ENNReal.ofReal (c ν^{3/2} e^{−CνS})` is positive and finite (`0 < c`,
`0 < ν`, `e^{·} > 0`, `ν^{3/2} > 0`), so `0` lies in the ball and — with the
D01 finiteness of the inhomogeneous norm (`forceSobolevENorm_ne_top`, lane 042)
— the ball is a genuine, non-vacuous neighbourhood of `0` in `𝓕_ℝ`.

## The datum is zero, so no spatial homogeneous norm is needed

Unlike R43 (`research/R43/Spec.lean`, whose `universal` field carries
`‖a‖_{Ḣ^{1/2}}` and therefore a local `dotHomogeneousENorm`), Proposition 4.4
fixes `a = 0`, so the manuscript's hypothesis mentions **only** the force norm.
This spec therefore needs **no** spatial homogeneous-norm object at all, and
carries no local `def`.
-/

noncomputable section

namespace BlowupDensity.R44.DraftB

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- **Proposition 4.4** (`prop:Rcritical2`, "Regularity on a prescribed finite
interval"), `paper/sections/04-whole-space.tex:136-144`, in the shape
`research/section4/STATEMENTS.md:562-624` fixes and `R41` consumes at `S = T`.

The two universal constants `c, C` are **fields**, hence quantified before every
`ν`, `S`, `f`, as `04-whole-space.tex:143` requires ("for suitable universal
positive constants `c, C`") and as risk note `STATEMENTS.md:594` insists (all of
`θ, C₀, C₂, C₃, c, C` are `ν`- and `S`-free).  The proof's internal constants
`θ, C₀, C₂, C₃` (`04-whole-space.tex:157,160,162`) are **not** exposed: they
belong to the smallness gate `Y ≤ θν` and the Grönwall coefficients, all
absorbed into the two exported constants `c, C`, exactly as the manuscript's
displayed radius `c ν^{3/2} e^{−CνS}` presents them.

The radius is inlined as `ENNReal.ofReal (c * ν ^ (3/2) * Real.exp (−(C*ν*S)))`
rather than carried as a separate `radius` field: `R41` consumes the dedicated
`nonDensityAtHorizon` field below (not a named radius function), and inlining
keeps the two constants `c, C` the *only* free data, so no implementation
freedom is introduced beyond the manuscript's own `c, C`.

Every field is either data (`c`, `C`) or a fully spelled-out manuscript
statement; no field is an abstract proposition variable, and no clause of
A02/A04/A05/C01/D01 is carried as a field, so the structure states exactly the
manuscript's theorem with no added rider. -/
structure RCritical2API where
  /-- `04-whole-space.tex:143`, "universal positive constants `c, C`": the
  scale of the smallness radius.  `ν`- and `S`-free (a field), shared by both
  conclusion fields below. -/
  c : ℝ
  /-- `04-whole-space.tex:143`, the exponential rate of the radius.  `ν`- and
  `S`-free. -/
  C : ℝ
  /-- `04-whole-space.tex:143`, "`c > 0`".  Load-bearing: without it `c ≤ 0`
  makes `ENNReal.ofReal (c * ν ^ (3/2) * Real.exp _) = 0`, the smallness
  hypothesis becomes unsatisfiable, and the structure would be inhabited by a
  statement with no content. -/
  hc : 0 < c
  /-- `04-whole-space.tex:143`, "`C > 0`".  Guarantees `r_{ν,S} = cν^{3/2}e^{−CνS}`
  is a genuine (decaying, not growing) radius as `S` grows. -/
  hC : 0 < C
  /-- **The theorem** (`04-whole-space.tex:136-144`):

    `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2})} < c ν^{3/2} e^{−CνS}`
      `⟹  T^ν_{max,ℝ}(0,f) > S`,

  for every `ν > 0` and every `S > 0`.

  * `f` ranges over `MemForceR` (`Data.lean:544`), the manuscript's `𝓕_ℝ`.
  * `forceSobolevENormL2 (-(1/2)) f` (`Data.lean:235` = `forceSobolevENorm 2
    (-1/2) f`, `Data.lean:225`) is `‖f‖_{L²(0,∞;H^{-1/2})}`, the **inhomogeneous**
    `q = 2` datum-path Bochner norm over `forceTimeMeasure`, i.e. over `(0,∞)` as
    `:140` requires.  It is **not** `Data.forceHomogeneousENorm 2 (-1/2)`; see
    fact 3 of the module docstring and "the vacuity trap" below.
  * The threshold `ENNReal.ofReal (c * ν ^ (3/2 : ℝ) * Real.exp (-(C * ν * S)))`
    is the manuscript's `r_{ν,S} = c ν^{3/2} e^{−CνS}` (`:143`).  It is positive
    and finite (`0 < c`, `0 < ν`, `ν ^ (3/2) > 0`, `Real.exp _ > 0`), so a force
    whose critical norm is `⊤` fails the hypothesis rather than meeting it.
  * `ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f` (`Data.lean:657`) is
    `T^ν_{max,ℝ}(0,f) > S`, the manuscript's literal conclusion (`:141`).

  **Why the lifespan inequality and not `RegularThrough`.**  `Data.RegularThrough
  ν 0 f S` (`Data.lean:664`) unfolds to `∃ δ > 0, Nonempty (ClassicalSolutionR ν
  0 f (S+δ))`; given `Data.maximalLifespanR`'s definition as
  `⨆ S', ⨆ _ : Nonempty (ClassicalSolutionR ν 0 f S'), ofReal S'`, the two are
  equivalent (`RegularThrough ⟹ lifespan ≥ ofReal (S+δ) > ofReal S`, and
  conversely `lt_iSup_iff` extracts a horizon `S' > S`).  The lifespan form is
  chosen because (a) it is the character-for-character transcription of "`T^ν_max
  > S`", and (b) it is the *literal negation* of `f ∈ Data.breakdownSetRZero ν S`
  (defined via `maximalLifespanR ν 0 f ≤ ofReal S`), so `R41` consumes it below
  with no massaging.

  *The proof route, for the record, owned elsewhere* (`04-whole-space.tex:145-174`).
  Test the projected equation against `J u`, `J = (I−Δ)^{1/2}`, with
  `Y = ‖u‖_{H^{1/2}}`, `Z = ‖∇u‖_{H^{1/2}}`, `B = ‖f‖_{H^{-1/2}}` — R44's own
  step (the exact weight identity `‖u‖²_{H^{3/2}} = Y² + Z²` and the duality
  `|⟨f,Ju⟩| ≤ B(Y²+Z²)^{1/2}` are R44's, `STATEMENTS.md:589-591`).  Lemma B.1's
  critical embeddings enter through A05:
  `research/A05/Spec.lean:214-216` (`Cbessel`, `‖Ju‖₃ ≤ C‖u‖_{H^{3/2}}`, "the
  inhomogeneous multiplier form Proposition 4.4 tests against"),
  `research/A05/Spec.lean:268` `homogeneousLeSobolev` (`‖z‖_{Ḣ^a} ≤ ‖z‖_{H^a}`
  at `a ∈ {1/2,1}`, the homogeneous→inhomogeneous comparison that turns Lemma
  B.1's homogeneous estimates into the inhomogeneous `Y, Z`), and
  `research/A05/Spec.lean:280` `dotThreeHalvesLeGradientSobolev`
  (`‖v‖_{Ḣ^{3/2}} ≤ ‖∇v‖_{H^{1/2}} = Z`).  Young's inequality gives eq:Rcritical2
  `(Y²)' + νZ² ≤ C₂νY² + C₃ν^{-1}B²` while `Y ≤ θν`, and Grönwall from `Y(0)=0`
  gives `Y(t)² ≤ C₃ν^{-1}e^{C₂νS}‖f‖²_{L²_tH^{-1/2}}` for `t ≤ S`; choosing the
  radius `< θ²ν²/4` contradicts a first crossing `Y = θν` (the continuity /
  first-exit argument, R44's own, `STATEMENTS.md:649`).  The continuation half
  reuses C01: `research/C01/Spec.lean` `enstrophyIntegralBound` (eq:RH1 `H¹`
  absorption once `‖u‖₃ ≤ ν/(4C₁)`), `l2Bound` (eq:RL2, here with `a = 0` so
  `K(S) = ∫₀ˢ‖f‖₂` and `‖∇a‖₂ = 0`), and `h2TimeIntegral` (the `∫₀ˢ‖u‖²_{H²} < ∞`
  assembly), fed to A04's continuation adapter
  (`research/A04/Spec.lean:296` region, `lifespanInfiniteOfLocallyFinite`) over
  the maximal-solution family of `research/A02/Spec.lean:210,421`
  (`IsMaximalSolution`), to exclude a maximal lifespan at or before `S`.  None of
  these quantities is a hypothesis of this field: the manuscript's theorem
  carries none.

  **The vacuity trap.**  Because the hypothesis fails safe to `⊤`, the danger is
  the opposite one: the statement is vacuous if `forceSobolevENormL2 (-1/2) f`
  were `⊤` for *every* `f ∈ 𝓕_ℝ`.  It is not.  The **inhomogeneous** finiteness
  `∀ f, MemForceR f → forceSobolevENorm 2 (-1/2) f ≠ ⊤` is proved (lane 042,
  `HalfOrder.lean` `forceSobolevENorm_ne_top`, general `s ≤ m`, `q ∈ {1,2}`;
  standard axioms) and applies here at `s = -1/2 ≤ 0 = m`, `q = 2`.  It is
  pending registration into the D01 datum-lemmas V2 contract, so it is not yet in
  this worktree's build closure, but it exists in Lean.  Had the hypothesis used
  the **homogeneous** `Data.forceHomogeneousENorm 2 (-1/2)`, its finiteness on
  `𝓕_ℝ` would be the *open* homogeneous twin (lane 042 GAP; a general-`H^∞`-slice
  homogeneous datum for the multiplier `|ξ|^{1/2}(1+|ξ|²)^{-1/4}`), and the
  statement would also be mathematically wrong (`:173`).  Using the inhomogeneous
  norm removes both problems at once. -/
  main :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-(1 / 2)) f
            < ENNReal.ofReal (c * ν ^ (3 / 2 : ℝ) * Real.exp (-(C * ν * S))) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f
  /-- **The consequence `R41` consumes, at `S = T`** (`STATEMENTS.md:133-136`):

    `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2})} < c ν^{3/2} e^{−CνT}`
      `⟹  f ∉ B^ℝ_{ν,0,T}`,

  for every `ν > 0` and every `T > 0`.  Equivalently, the open ball of radius
  `r_{ν,T}` about `0` in the `L²_tH^{-1/2}` norm "contains no element of
  `B^ℝ_{ν,0,T}` (each such `f` has `T^ν_{max,ℝ}(0,f) > T`)"
  (`STATEMENTS.md:134-135`).

  This is the single consequence `R41` consumes: `RMainAPI.nonDensityZero` at
  `q = 2` (`STATEMENTS.md:160-164`) uses it as the `s = -1/2` base case and then
  spreads it to every `s ≥ -1/2` via `‖·‖_{H^{-1/2}} ≤ ‖·‖_{H^s}`
  (`STATEMENTS.md:136`), yielding non-density in the `L²_tH^s` metric for the
  whole endpoint-inclusive range `s ≥ s_2 = -1/2` (`04-whole-space.tex:179`).

  Kept as its own field (rather than left for `R41` to derive from `main`), on
  `STATEMENTS.md:626`'s instruction, so that `R41` needs no massaging: the
  conclusion `f ∉ breakdownSetRZero ν T` is exactly the `not_mem` `R41` wants.
  It is a one-line specialisation of `main` at `S := T` (unfolding
  `Data.breakdownSetRZero`/`breakdownSetR`/`breakdownSetIn`, `Data.lean:672-687`:
  `f ∈ B^ℝ` is `MemForceR f ∧ maximalLifespanR ν 0 f ≤ ofReal T`, whose negation
  under `MemForceR f` is `maximalLifespanR ν 0 f > ofReal T`), unlike R43's
  `inhomogeneousAtZero`, which additionally reduced a homogeneous norm to an
  inhomogeneous one and set `a = 0` — here `a = 0` and the inhomogeneous norm are
  already in `main`. -/
  nonDensityAtHorizon :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-(1 / 2)) f
            < ENNReal.ofReal (c * ν ^ (3 / 2 : ℝ) * Real.exp (-(C * ν * T))) →
          f ∉ breakdownSetRZero ν T

end BlowupDensity.R44.DraftB
