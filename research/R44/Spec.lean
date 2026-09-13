import Contracts.V1.Data

/-!
# R44 reconciled specification: Proposition 4.4, `prop:Rcritical2`

**Regularity on a prescribed finite interval** — the `L²(0,∞;H^{-1/2})` critical
force threshold at zero initial velocity.
Statement `paper/sections/04-whole-space.tex:136-144`; proof `:145-174`.
Graph node `R44 ← A04, A05, C01` (same three children as R43,
`research/section4/STATEMENTS.md:598`), transitively `← A02` through A04's
continuation clause and `← D01` for the data objects; consumer `R44 → R41`
(Theorem 4.1), used **only** at `S = T` (`04-whole-space.tex:179`).
Ledger: `research/section4/STATEMENTS.md` §4 (`:556-651`), skeleton `:611-624`;
R41's consumption `:133-136`.

Reconciliation of `DraftA.lean` (`RCritical2API`, 9 fields, `radius` as a named
function pinned by `radiusFormula`) and `DraftB.lean` (`RCritical2API`, 4 fields,
radius inlined) against the paper and the sibling specs as they actually stand
on this branch.  Decisions and their reasons: `research/R44/RECONCILIATION.md`;
field-by-field and gap tables: `research/R44/COMPARISON.md`.

This file is a **specification**.  It contains one `structure`, no `def` and no
proof term; it assumes nothing and introduces no `axiom`, no `sorry`, no
`native_decide` and no abstract `Prop` placeholder field.  Both propositional
fields are fully spelled-out statements about named `Contracts.V1.Data` objects.

## The statement (`04-whole-space.tex:136-144`)

> For each `ν, S > 0` there is `r_{ν,S} > 0` such that
> `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2}(ℝ³))} < r_{ν,S}  ⟹  T^ν_{max,ℝ}(0,f) > S`.
> One can take `r_{ν,S} = c ν^{3/2} e^{−C ν S}` for suitable universal positive
> constants `c, C`.

Quantifier order (`STATEMENTS.md:569`), transcribed exactly:

    ∃ c, C > 0, ∀ ν, S > 0, ∀ f ∈ 𝓕_ℝ,
      (‖f‖_{L²(0,∞;H^{-1/2})} < c ν^{3/2} e^{−CνS}  ⟹  T^ν_{max,ℝ}(0,f) > S).

`c` and `C` are **fields**, hence chosen before every `ν`, `S`, `f`
(`:143`, `STATEMENTS.md:594`: `θ, C₀, C₂, C₃, c, C` are all `ν`- and `S`-free).
The radius depends on **both** `ν` and `S` and on **no** `f`; its `S`-dependence
is genuine and exponential (`:173`, "The radius depends on `S`"), which is why
the `q = 2` result is *interval* regularity and Proposition 4.3 is global.

## Four load-bearing facts, each of which a careless formalisation gets wrong

1. **The initial velocity is exactly zero** (`:139,141`, risk note
   `STATEMENTS.md:631-632`, "`a = 0` is essential").  Grönwall starts from
   `Y(0) = 0`; a general `a` would carry a `Y(0)²e^{C₂νS}` term and the radius
   would depend on `a`.  The datum is spelled `fun _ => 0`, exactly as
   `Data.breakdownSetRZero` unfolds it (`Data.lean:686-687`), so the `R41`
   consequence below reaches `B^ℝ_{ν,0,T}` with no conversion.  Because the datum
   is zero there is **no spatial homogeneous norm** here and, unlike
   `research/R43/Spec.lean`, no local `def` at all.

2. **The force norm is the INHOMOGENEOUS `H^{-1/2}` norm, integrated in `L²`
   over `(0,∞)`** (`:140`), never the homogeneous `Ḣ^{-1/2}` one.  The paper
   states the reason in as many words (`:173`): *"The inhomogeneous norm is
   essential here because smallness in `H^{-1/2}` does not control the
   homogeneous negative norm at low frequencies."*  A homogeneous hypothesis
   would state a proposition **false as proved**, and would additionally route
   through a finiteness that is still open (lane 042's homogeneous GAP), making
   the field vacuous meanwhile.  The object used is therefore
   `Data.forceSobolevENormL2 (-1 / 2) f` (`Data.lean:235`, the `q = 2`
   abbreviation of `Data.forceSobolevENorm`, `:225`), the measurable-datum-path
   Bochner norm over `forceTimeMeasure = (0,∞)`, and **not**
   `Data.forceHomogeneousENorm 2 (-1 / 2)` (`Data.lean:390`).

3. **The conclusion is the strict lifespan inequality `T^ν_{max,ℝ}(0,f) > S`**
   (`:141`) — regularity up to a prescribed finite horizon, not global
   regularity (contrast R43's `= ⊤`) and not `Data.RegularThrough`.  Written
   `ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f` (`Data.lean:657`).
   `RegularThrough ν (fun _ => 0) f S` (`Data.lean:664`) is provably equivalent —
   `ofReal S < ⨆_{S'} ⨆_{Nonempty (ClassicalSolutionR … S')} ofReal S'` holds iff
   some horizon `S' > S` carries a solution — but the lifespan form is chosen
   because (a) it is the character-for-character transcription of the paper's
   `T^ν_{max} > S`, (b) it is the *definitional negation* of
   `f ∈ Data.breakdownSetRZero ν S`, so `R41` consumes it with no massaging, and
   (c) it is literally what A04 hands over: `research/A04/Spec.lean:613`
   `extendsBeyond` concludes `ENNReal.ofReal S < maximalLifespanR ν a f`, and its
   docstring (`:592-594`) says "**This is the field `prop:Rcritical2` uses**".

4. **`f ∈ 𝓕_ℝ` is load-bearing beyond the smallness**
   (`:171`, risk note `STATEMENTS.md:633-638`).  The continuation half uses that
   `‖f‖_{L¹_tL²_x}` and `‖f‖_{L²_tL²_x}` are **finite**, "even though they are
   not required to be small".  So `MemForceR f` is a genuine hypothesis, not
   bookkeeping: the proposition is *not* a statement about an abstract
   `H^{-1/2}` ball, which is exactly why Theorem 4.1's converse yields a
   *relative* open ball in the smooth class.

## Conventions

Every quantified object is `verification/Contracts/V1/Data.lean`'s:
`MemForceR` is `𝓕_ℝ` (`Data.lean:544`, eq:Rclasses `02-preliminaries.tex:17`);
`forceSobolevENormL2 s f` is `‖f‖_{L²(0,∞;H^s(ℝ³))}` (`Data.lean:235`);
`maximalLifespanR ν a f` is `T^ν_{max,ℝ}(a,f)`, valued in `[0,∞]` with `⊤` for
global regularity (`Data.lean:657`, `02-preliminaries.tex:32`);
`breakdownSetRZero ν T` is `B^ℝ_{ν,0,T} = {f ∈ 𝓕_ℝ : T^ν_{max,ℝ}(0,f) ≤ T}`
(`Data.lean:686`, eq:Rsingularforces `02-preliminaries.tex:42`).
Time is the first spacetime coordinate; the force time norm runs over `(0,∞)`.

**Two spellings are load-bearing and were pinned by experiment, not by taste.**

* The critical order is `-1 / 2`, which Lean parses as `(-1) / 2`.  It is **not**
  definitionally `-(1 / 2)`: `example : (-1/2 : ℝ) = -(1/2) := rfl` fails.  Since
  the order indexes a *type* (`RealVectorSobolev s` inside
  `Data.forceSobolevENorm`), mixing the two spellings costs a transport, not a
  rewrite.  `-1 / 2` is the spelling of the frozen V1 contract
  `Contracts/V1/Thresholds.lean:15,16,17` (`l2`, `negativeIndex`) and of the
  ledger skeleton `STATEMENTS.md:622`, so it is the one used here.
  `forceSobolevENormL2 (-1 / 2) f = forceSobolevENorm 2 (-1 / 2) f` holds by
  `rfl`.
* The exponent is `ν ^ (3 / 2 : ℝ)`, i.e. `Real.rpow ν (3 / 2)` (checked by
  `rfl`), and the ascription `(… : ℝ)` is what makes it so; `ν ^ (3 / 2 : ℕ)`
  would silently be `ν ^ 1`.

**Every norm is `ℝ≥0∞`-valued and none is routed through `.toReal`**, so a force
with no measurable `H^{-1/2}` datum path fails safe to `⊤`, the smallness
hypothesis then fails, and the statement is never satisfied by accident.  The
threshold `ENNReal.ofReal (radius ν S)` is positive and finite (`radiusPos`), so
the ball is a genuine neighbourhood of `0` rather than empty: `0 ∈ 𝓕_ℝ` has norm
`0`, and by lane 042's `forceSobolevENorm_ne_top`
(`formalization/NSFormalization/Section4/D01/HalfOrder.lean:156`, general
`s ≤ (m : ℕ)`, `q ∈ {1,2}`, standard axioms) *every* `f ∈ 𝓕_ℝ` has a finite
`L²_tH^{-1/2}` norm — the `m := 0`, `s := -1 / 2`, `q := 2` instance, `-1/2 ≤ 0`.
That theorem is proved but not yet a registered contract field
(`Contracts/V1/DatumLemmas.lean:169` registers only the *spatial*
`smoothJets_sobolevENorm_ne_top`); see `RECONCILIATION.md` §5 item **G-Reg**.

## The proof route, for the record (owned elsewhere; no field below mentions it)

`04-whole-space.tex:145-174`.  With `J = (I−Δ)^{1/2}`, `Y = ‖u‖_{H^{1/2}}`,
`Z = ‖∇u‖_{H^{1/2}}`, `B = ‖f‖_{H^{-1/2}}` and the **exact** weight identity
`‖u‖²_{H^{3/2}} = Y² + Z²`, testing the projected equation against `Ju` and
Fourier Cauchy–Schwarz give eq:Rcritical2 `(Y²)' + νZ² ≤ C₂νY² + C₃ν^{-1}B²`
while `Y ≤ θν`.  Grönwall from `Y(0) = 0` yields
`Y(t)² ≤ C₃ν^{-1}e^{C₂νS}‖f‖²_{L²_tH^{-1/2}}` for `t ≤ S` while `Y ≤ θν`;
choosing `r_{ν,S}` so that this is `< θ²ν²/4` makes a first crossing `Y = θν`
contradictory (`:169`, an implicit first-exit-time argument on
`[0, min(S, T_max))`).  Then `‖u‖₃ ≤ CY ≤ Cθν` discharges the `H¹` absorption
eq:RH1, and eq:RL2 plus the `∫₀^S‖u‖²_{H²} < ∞` assembly at `a = 0`
(`K(S) = ∫₀^S‖f‖₂`, `‖∇a‖₂ = 0`) feed A04's continuation to exclude a maximal
lifespan at or before `S`.  Owners:

| consumed | owner, as it actually stands on this branch |
|---|---|
| `‖u‖₃ ≤ C(1/2)‖u‖_{Ḣ^{1/2}}`, `‖∇u‖₃+‖Λu‖₃ ≤ C‖u‖_{Ḣ^{3/2}}`, `‖∇u‖₆ ≤ C‖Δu‖₂` | `research/A05/Spec.lean:366,384,396` |
| `‖Jv‖₃ ≤ Cbessel‖v‖_{H^{3/2}}`, the inhomogeneous multiplier form | `research/A05/Spec.lean:216,406` |
| `‖z‖_{Ḣ^a} ≤ ‖z‖_{H^a}`, `‖v‖_{Ḣ^{3/2}} ≤ ‖∇v‖_{H^{1/2}}` (`Y, Z` are inhomogeneous) | `research/A05/Spec.lean:268,280` |
| eq:RL2, eq:RH1 | `research/C01/Spec.lean:383,510,532` |
| the `∫₀^S‖u‖²_{H²}` assembly **at `a = 0`** | `research/C01/Spec.lean:599` `h2TimeIntegralZeroDatum` |
| continuation at the prescribed finite `S` | `research/A04/Spec.lean:613` `extendsBeyond` |
| the maximal-solution family behind `maximalLifespanR` | `research/A02/Spec.lean:210,421` |

The proof's internal constants `θ, C₀, C₂, C₃` and the two shrinkings of `θ`
(`:157,160,171`) are **not** exposed as fields: they belong to the smallness gate
`Y ≤ θν` and the Grönwall/absorption bookkeeping that produce the two universal
constants `c, C` of the radius, and `STATEMENTS.md:645-648` records that the
paper's outline does not even pin `C₂, C₃`.  The contract offers only `c, C`.
-/

noncomputable section

namespace BlowupDensity.R44.Draft

open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- **Proposition 4.4** (`prop:Rcritical2`, "Regularity on a prescribed finite
interval"), `paper/sections/04-whole-space.tex:136-144`, in the shape the ledger
skeleton `research/section4/STATEMENTS.md:611-624` fixes and `R41` consumes at
`S = T` (`04-whole-space.tex:179`).

Every field is either data (`c`, `C`, `radius`), a positivity the manuscript
asserts (`hc`, `hC`, `radiusPos`), the pin that turns `radius` into an
abbreviation of `c` and `C` (`radiusFormula`), or a fully spelled-out manuscript
statement (`main`, `nonDensityBallZero`).  No field is an abstract proposition
variable, and no clause of A02/A04/A05/C01/D01 is restated here, so the structure
carries exactly the manuscript's theorem with no added rider — the R43 decision
(`research/R43/RECONCILIATION.md` §1) applied unchanged. -/
structure RCritical2API where
  /-- `04-whole-space.tex:143`, "for suitable universal positive constants
  `c, C`": the leading coefficient of the smallness radius, in units of `ν^{3/2}`.
  A single real, `ν`- and `S`-free because it is a field and therefore bound
  before every `ν`, `S`, `f` (`STATEMENTS.md:594`). -/
  c : ℝ
  /-- `04-whole-space.tex:143`: the exponential rate in `e^{−C ν S}`.  A single
  real, `ν`- and `S`-free.  It is what makes the radius shrink as `νS` grows —
  the "regular neighborhood whose radius depends on `T`" of `:16` and `:173`.
  Kept as a field rather than hidden under an existential inside `radiusFormula`
  precisely so that it is bound before `ν` and `S`: `R41`'s non-density ball must
  scale uniformly in the fixed `ν, T` it is instantiated at. -/
  C : ℝ
  /-- `04-whole-space.tex:143`, "`c > 0`".  Load-bearing: with `c ≤ 0` the radius
  would be `≤ 0`, `ENNReal.ofReal (radius ν S) = 0`, both smallness hypotheses
  would be unsatisfiable, and the structure would be inhabited by two vacuously
  true statements. -/
  hc : 0 < c
  /-- `04-whole-space.tex:143`, "`C > 0`".  Unlike `hc` this cannot be violated
  in the direction of vacuity — any real `C` leaves the radius positive — so it
  is a faithfulness marker rather than a guard: it records the manuscript's claim
  that the radius **decays** in `νS`, on which the `:16` remark and
  `STATEMENTS.md:641-644` ("the non-density ball shrinks as `T` grows") rest. -/
  hC : 0 < C
  /-- The smallness radius `r_{ν,S}` of `04-whole-space.tex:137`, as a named
  function of `ν` and `S`.

  Kept as a field rather than inlined, following the ledger skeleton
  (`STATEMENTS.md:611-624`, with the reason spelled out at `:626-627`: "Keeping
  `radius` as a field (rather than inlining the formula) lets
  `RMainAPI.nonDensityZero` consume `radius ν T` without re-deriving `c, C`").
  It introduces **no** implementation freedom — `radiusFormula` below pins it at
  every real `ν, S` — and it makes the two
  conclusion fields carry the *same* threshold by construction rather than by
  two copies of one formula that could drift apart. -/
  radius : ℝ → ℝ → ℝ
  /-- `04-whole-space.tex:143`: `r_{ν,S} = c ν^{3/2} e^{−C ν S}`.

  `ν ^ (3 / 2 : ℝ)` is `Real.rpow ν (3 / 2)` (the ascription is load-bearing: a
  natural exponent would silently truncate), and `Real.exp (-(C * ν * S))` is
  `e^{−CνS}`.  Stated at every real `ν, S`, so `radius` is determined by `c` and
  `C` alone and the structure is equivalent to the one that inlines this formula
  in `main` and `nonDensityBallZero`. -/
  radiusFormula : ∀ ν S : ℝ,
    radius ν S = c * ν ^ (3 / 2 : ℝ) * Real.exp (-(C * ν * S))
  /-- `04-whole-space.tex:137`, "there is `r_{ν,S} > 0`": the radius is strictly
  positive on the manuscript's regime `ν, S > 0`, so `ENNReal.ofReal (radius ν S)`
  is a positive finite threshold and the ball `{f : ‖f‖ < radius ν S}` is a
  genuine neighbourhood of `0` rather than the empty set.

  Derivable from `radiusFormula` and `hc` in one line
  (`mul_pos (mul_pos hc (Real.rpow_pos_of_pos hν _)) (Real.exp_pos _)`, which does
  not even use `0 < S`); carried as a field for the reason R43 carries
  `inhomogeneousAtZero` (`research/R43/RECONCILIATION.md` §3) — the consumer
  `RMainAPI.nonDensityZero`, whose shape is `∃ ρ, 0 < ρ ∧ …`
  (`STATEMENTS.md:160-163`), should perform no reduction. -/
  radiusPos : ∀ ν S : ℝ, 0 < ν → 0 < S → 0 < radius ν S
  /-- **The theorem** (`04-whole-space.tex:136-144`):

    `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2})} < r_{ν,S}  ⟹  T^ν_{max,ℝ}(0,f) > S`,

  for every `ν > 0` and every `S > 0`.

  * `f` ranges over `MemForceR` (`Data.lean:544`), the manuscript's `𝓕_ℝ`.  This
    hypothesis is load-bearing beyond the smallness: the continuation half uses
    the **finiteness** (not smallness) of `‖f‖_{L¹_tL²_x}` and `‖f‖_{L²_tL²_x}`
    (`:171`, `STATEMENTS.md:633-638`), so the proposition is a statement about
    the smooth class, not about an abstract `H^{-1/2}` ball.
  * The initial velocity is `fun _ => 0` — exactly zero (`:139,141`); it is not
    quantified, and the spelling is `Data.breakdownSetRZero`'s
    (`Data.lean:686-687`).
  * `forceSobolevENormL2 (-1 / 2) f` (`Data.lean:235` = `forceSobolevENorm 2
    (-1 / 2) f`, `:225`) is `‖f‖_{L²(0,∞;H^{-1/2})}`, the **inhomogeneous**
    measurable-datum-path Bochner norm over `forceTimeMeasure`, i.e. over `(0,∞)`
    as `:140` requires — **not** `Data.forceHomogeneousENorm 2 (-1 / 2)`, which
    `:173` says does not control the force.  See fact 2 of the module docstring.
  * The threshold `ENNReal.ofReal (radius ν S)` is positive and finite
    (`radiusPos`), so an `f` whose critical norm is `⊤` fails the hypothesis
    rather than meeting it, and the ball is non-vacuous by lane 042's
    `forceSobolevENorm_ne_top` at `m := 0`, `q := 2`.
  * `ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f` (`Data.lean:657`) is
    `T^ν_{max,ℝ}(0,f) > S`.  `maximalLifespanR` is the supremum of the horizons
    that carry an actual `ClassicalSolutionR`, so it cannot be inflated by a
    field that is not a solution: no implementation satisfies this with a
    solution that breaks down at or before `S`. -/
  main :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f
  /-- **The single consequence `R41` consumes**, the `S = T` instance
  (`04-whole-space.tex:179`, "For `q = 2`, use Proposition 4.4 with `S = T`";
  `STATEMENTS.md:133-136`):

    `f ∈ 𝓕_ℝ`, `‖f‖_{L²(0,∞;H^{-1/2})} < r_{ν,T}  ⟹  f ∉ B^ℝ_{ν,0,T}`,

  for every `ν > 0` and every `T > 0` — the ledger's "there is `r_{ν,T} > 0` such
  that `{f ∈ 𝓕_ℝ : ‖f‖_{L²_tH^{-1/2}} < r_{ν,T}}` contains no element of
  `B^ℝ_{ν,0,T}`".  `ν` and `T` are quantified here although `RMainAPI` fixes them
  as fields (`STATEMENTS.md:144`), so that R41 instantiates rather than
  transports.

  `f ∈ breakdownSetRZero ν T` is, by `Iff.rfl`,
  `MemForceR f ∧ maximalLifespanR ν (fun _ => 0) f ≤ ENNReal.ofReal T`
  (`Data.lean:686 → 678 → 672`), so this field is the exact negation of the
  breakdown condition and needs no unfolding on the consumer side.  Because
  membership in `B^ℝ_{ν,0,T}` already supplies `MemForceR f`, the shape
  `RMainAPI.nonDensityZero` wants — `∀ f ∈ B^ℝ_{ν,0,T}, ofReal (radius ν T) ≤
  ‖f‖_{L²_tH^{-1/2}}` — follows by contraposition with no extra hypothesis; from
  there `‖·‖_{H^{-1/2}} ≤ ‖·‖_{H^s}` spreads it to every `s ≥ -1/2 = s_2`
  (`:179`, `STATEMENTS.md:136`).

  Kept as its own field rather than left for `R41` to derive from `main`, on the
  same ground R43 keeps `inhomogeneousAtZero` (`STATEMENTS.md:522`,
  `research/R43/Spec.lean`): the consumer performs no reduction.  Here the
  reduction saved is only the instantiation `S := T` plus the contradiction
  between `ofReal T < maximalLifespanR …` and the `≤ ofReal T` inside
  `breakdownSetRZero` — smaller than R43's, because `a = 0` and the inhomogeneous
  norm are already in `main`. -/
  nonDensityBallZero :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν T) →
          f ∉ breakdownSetRZero ν T

end BlowupDensity.R44.Draft
