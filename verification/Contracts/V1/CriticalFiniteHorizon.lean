import Contracts.V1.Data

/-!
# Contract: Proposition 4.4 finite-horizon critical regularity

Version one registers Proposition 4.4 (`prop:Rcritical2`) exactly in the
nine-field shape of `research/R44/Spec.lean:169-304`.  Every norm and solution
object is the canonical `Contracts.V1.Data` definition; no implementation
module is imported here.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.CriticalFiniteHorizon

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
structure CriticalFiniteHorizonAPI where
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

end BlowupDensity.Contracts.V1.CriticalFiniteHorizon
