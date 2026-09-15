import Contracts.V1.Data

/-!
# R43 draft specification A: global regularity for small critical data and `L¹` force

Task `R43`, Proposition 4.3 (`prop:Rcritical1`, "Global regularity for small
critical data and `L¹` force"), `paper/sections/04-whole-space.tex:82-133`.
Graph node `R43 ← A02, A04, A05, C01`; consumer `R43 → R41`
(`research/section4/STATEMENTS.md:428-556`, ledger §3).

This file is a **specification draft only**.  It contains `def`s and one
`structure`; it proves nothing with mathematical content, assumes nothing, and
introduces no `axiom`, no `sorry`, no `native_decide` and no abstract `Prop`
placeholder field.  Every propositional field is a fully spelled-out statement
about explicitly named `Contracts.V1.Data` objects.

## The statement

`04-whole-space.tex:82-89`: **there is a universal `c > 0`** such that for every
viscosity `ν > 0`, every `a ∈ X_R` and every `f ∈ F_R`,

    ‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹(0,∞;Ḣ^{1/2})} < c ν   ⟹   T^ν_{max,R}(a,f) = ∞.

In particular (`:88`, `:132`), for `a = 0` the inhomogeneous ball
`‖f‖_{L¹(0,∞;H^{1/2})} < c ν` consists of globally regular inputs, using
`‖z‖_{Ḣ^{1/2}} ≤ ‖z‖_{H^{1/2}}`.  The quantifier order is
`∃ c > 0, ∀ ν > 0, ∀ a ∈ X_R, ∀ f ∈ F_R, …`
(`research/section4/STATEMENTS.md:441`); `c` is a single `ℝ` bound **outside**
every `ν`, `a`, `f`, so the smallness threshold scales as `c ν`.

`R41` consumes from R43 *exactly one consequence*
(`research/section4/STATEMENTS.md:128-135`): the field `inhomogeneousAtZero`,
via `RMainAPI.nonDensityZero` at `q = 1`.  Both consequence fields
(`universal`, `inhomogeneousAtZero`) use the **same** `c`.

## What is consumed, and how it is expressed

Because `research/A02/Spec.lean`, `research/A04/Spec.lean`,
`research/A05/Spec.lean` and `research/C01/Spec.lean` are drafts under
`research/` and not Lean library modules, none can be `import`ed by a file
checked with `cd verification && lake env lean ../research/R43/DraftA.lean`.
The clauses R43's proof consumes are therefore **restated verbatim** as fields
of `CriticalRegularityL1API`, each tagged `⟪Source:field⟫` with a comment
naming its owner, exactly as `research/A02/Spec.lean` restates the three
`LocalTheoryAPI` fields it consumes as `⟪A01:…⟫`.  When A02/A04/A05/C01 are
registered under `verification/Contracts/`, these fields become
`import`ed-API fields.  `A02` and `A05` already exist as accepted drafts;
`A04` and `C01` do not yet exist, so their clauses below are the *first written
shape* of what those specs must export — `research/R43/COMPARISON_A.md` §"clause
gaps" collects them.

The proof route (`research/section4/STATEMENTS.md:486-500`):

* **(A05)** the critical embedding `‖u‖₃ ≤ C‖u‖_{Ḣ^{1/2}}` — `velocityCriticalL3`;
* **(R43 core)** the critical-norm bound `y(t) = ‖u(t)‖_{Ḣ^{1/2}} ≤ c ν` on the
  whole lifespan (`eq:Rcritical1`, regularised norm division, continuity
  bootstrap, `:97-104`) — `criticalNormBound`;
* combining, the intermediate bound `‖u(t)‖₃ ≤ C c ν` — `velocityL3Small`,
  the whole-space analogue of Proposition 4.4's `‖u‖₃ ≤ Cθν` step;
* **(C01)** the assembled squared-`H²` time integral
  `∫₀^S ‖u‖²_{H²} dt < ∞` on every finite `S ≤ T_max` (`eq:RL2`, `eq:RH1` and
  the `H²` Fourier inequality, `:106-131`) — `h2SquaredIntegralFinite`;
* **(A04)** the continuation criterion `eq:criterion`: a solution on `[0,S)`
  with `∫₀^S ‖u‖²_{H²} < ∞` extends past `S` (`02-preliminaries.tex:108`) —
  `continuation`;
* **(A02)** existence of the maximal solution and the no-extension
  characterisation of its lifespan (`02-preliminaries.tex:32,105`) —
  `existsMaximal`, `lifespanLeIffNoExtension`.

Together `continuation`, `h2SquaredIntegralFinite`, `existsMaximal` and
`lifespanLeIffNoExtension` exclude every finite maximal lifespan, which is the
proof's final line ("Proposition 2.1 excludes every finite maximal lifespan",
`:131`).  The three A05 embeddings the ledger records — `velocityCriticalL3`,
`derivativeCriticalL3` (`‖∇u‖₃ + ‖Λu‖₃ ≤ Cz`) and `gradientLSix`
(`‖∇u‖₆ ≤ C‖Δu‖₂`) — are used inside `criticalNormBound` and inside C01's
`eq:RH1`; only `velocityCriticalL3` is exposed here, because it is the clause
directly producing the `‖u‖₃` step, and the effect of the other two is captured
by `criticalNormBound` and `h2SquaredIntegralFinite`
(`research/R43/COMPARISON_A.md` records the full A05 consumption).

## Conventions, all inherited from `Contracts.V1.Data`

`initialClassR` is `X_R = H^∞ ∩ L²_σ` (`02-preliminaries.tex:12` eq:Rinitial),
`MemForceR` is `F_R` (`:17` eq:Rclasses), `maximalLifespanR ν a f` is
`T^ν_{max,R}(a,f) ∈ [0,∞]` with `= ⊤` meaning global regularity (`:32`),
`ClassicalSolutionR ν a f S` is the classical solution on `[0,S)`,
`forceHomogeneousENorm 1 (1/2) f` is `‖f‖_{L¹(0,∞;Ḣ^{1/2})}`,
`forceSobolevENormL1 (1/2) f = forceSobolevENorm 1 (1/2) f` is
`‖f‖_{L¹(0,∞;H^{1/2})}`, and `sobolevENorm 2 z` is `‖z‖_{H²}`.  Time is the
first spacetime coordinate.  Every norm is `ℝ≥0∞`-valued and no norm is routed
through `.toReal`, so a failure to have a datum fails safe to `⊤` (smallness
then fails) rather than to a junk `0`.

Three objects are defined here because `Data.lean` does not provide them on a
physical field and R43 needs them; each is a verbatim copy of a sibling draft's
definition, with provenance:

* `dotHomogeneousENorm` — `research/A05/Spec.lean:131`, the datum-infimum
  realisation of `‖·‖_{Ḣ^s}` on a physical field.  It is used **instead of**
  `Data.dotHHalfENorm` (`Contracts/V1/Data.lean:427`): that abbreviation is the
  literal pointwise Fourier integral `Data.homogeneousFourierENorm`, whose own
  docstring (`:401-419`) forbids its use on a general `H^∞` slice, where it
  totalises to a junk `0`.  A junk-`0` spatial norm would make the smallness
  hypothesis *vacuously satisfiable* by a large-data `a ∈ X_R` that is not
  `L¹`, so the datum-infimum form is required for the hypothesis to be tight
  (`research/R43/COMPARISON_A.md` records this as a `Data.lean` gap).
* `IsMaximalSolution`, `presingularTimes` — `research/A02/Spec.lean:210,168`,
  the maximal-solution predicate and the times strictly below the lifespan.
-/

noncomputable section

namespace BlowupDensity.R43.DraftA

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Objects R43 needs that `Data.lean` does not define on a physical field

Each is a verbatim copy of an accepted sibling draft (A05, A02); see the module
header for why `Data.lean`'s own objects are not used. -/

/-- ⟪A05:dotHomogeneousENorm⟫ (`research/A05/Spec.lean:131`,
`appendix-b-embeddings.tex:26-27`): `‖z‖_{Ḣ^s}` **for a physical field**, the
`L²` norm of the order-`s` homogeneous datum of the tempered vector
distribution the field represents, and `⊤` when the field has no such datum.
The empty infimum in `ℝ≥0∞` is `⊤`, so this is total and fail-safe.

This is the datum-infimum realisation, faithful on every `H^∞` field, and is
deliberately **not** `Data.dotHHalfENorm`/`Data.homogeneousFourierENorm`, whose
docstring (`Contracts/V1/Data.lean:401-419`) forbids the pointwise Fourier
integral on a general `H^∞` slice.  For `a ∈ X_R` it equals `‖a‖_{Ḣ^{1/2}}` and
is finite because `‖a‖_{Ḣ^{1/2}} ≤ ‖a‖_{H^{1/2}} < ∞`
(`research/section4/STATEMENTS.md:463-467`). -/
def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

/-- ⟪A02:presingularTimes⟫ (`research/A02/Spec.lean:168`,
`02-preliminaries.tex:32`): the times strictly before the maximal classical
lifespan, `[0, T^ν_{max,R}(a,f))` read inside `ℝ`.  `maximalLifespanR` is
`ℝ≥0∞`-valued, so the comparison is after `ENNReal.ofReal`; strictness is the
right condition, a solution existing on `[0,S)` for every `S` below the
supremum. -/
def presingularTimes (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < maximalLifespanR ν a f}

/-- ⟪A02:IsMaximalSolution⟫ (`research/A02/Spec.lean:210`,
`02-preliminaries.tex:32,105`): `(u,p)` **is** the maximal classical solution
for the datum `(ν,a,f)` — the lifespan is positive, and `u`, `p` are literally
the velocity and pressure of a classical solution on `[0,S)` for every `S`
strictly below the maximal lifespan.  The positivity clause is not decorative:
without it the second clause is vacuously true when the datum carries no
solution, since the empty supremum of `maximalLifespanR` is `0`
(`Contracts/V1/Data.lean:657`). -/
def IsMaximalSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanR ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanR ν a f →
      ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p

/-! ## 2. The contract -/

/-- Proposition 4.3 (`prop:Rcritical1`), `paper/sections/04-whole-space.tex:82-133`,
in the form `R41` consumes it, together with the sibling-API clauses R43's
proof passes through.

**Universal constants first.**  `c` and `Cemb` are `ℝ` fields of the structure,
hence quantified **outside** every `ν`, `a`, `f` and every solution: the paper's
"universal `c`" (`:83`) and the embedding constant of `appendix-b-embeddings.tex:14-15`
depend "only on the fixed exponents, domain and norm conventions, not on the
field or its frequency support" (`:109-110`). -/
structure CriticalRegularityL1API where
  /-- `04-whole-space.tex:83`, the **universal** smallness constant `c > 0`.  The
  proof shrinks it twice — `c < 1/(4C₀)` (`:104`) and again so that `C₁y ≤ ν/4`
  (`:112`); both shrinkings are `ν`-free because `y ≤ c ν`, which is why `c` is
  a bare `ℝ` outside the `∀ ν` binder (`research/section4/STATEMENTS.md:483-485`). -/
  c : ℝ
  /-- `04-whole-space.tex:83`, `c > 0`. -/
  hc : 0 < c
  /-- ⟪A05:C (1/2)⟫ (`appendix-b-embeddings.tex:14-15`, `04-whole-space.tex:93`):
  the universal constant of `‖u‖₃ ≤ C‖u‖_{Ḣ^{1/2}}`.  A field of the structure,
  so it too precedes every datum. -/
  Cemb : ℝ
  /-- `appendix-b-embeddings.tex:12-13`, `Cemb > 0`. -/
  hCemb : 0 < Cemb
  /-- **The theorem** (`04-whole-space.tex:84-87`): with `c` fixed above, for
  every `ν > 0`, every `a ∈ X_R` and every `f ∈ F_R`, the critical smallness
  `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹(0,∞;Ḣ^{1/2})} < c ν` forces global regularity
  `T^ν_{max,R}(a,f) = ∞`.

  `a` is quantified over `X_R`, not fixed and not zero (`:83`,
  `research/section4/STATEMENTS.md:441-443`).  The force time norm runs over
  `(0,∞)` and is the **homogeneous** `Ḣ^{1/2}` norm at exponent `q = 1`
  (`forceHomogeneousENorm 1 (1/2) f`).  The left side is `ℝ≥0∞`-valued, so if a
  datum lacks an `Ḣ^{1/2}` realisation the norm is `⊤` and the smallness fails,
  never a false pass. -/
  universal : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
    ∀ f : SpaceTimeField, MemForceR f →
      dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
          < ENNReal.ofReal (c * ν) →
        maximalLifespanR ν a f = ⊤
  /-- **The `R41` consequence** (`04-whole-space.tex:88`, `:132`,
  `research/section4/STATEMENTS.md:128-135`): the "in particular" clause, with
  the **same** `c`.  For zero initial velocity, every `f ∈ F_R` in the
  *inhomogeneous* ball `‖f‖_{L¹(0,∞;H^{1/2})} < c ν` is globally regular; the
  reduction to `universal` is `‖f‖_{Ḣ^{1/2}} ≤ ‖f‖_{H^{1/2}}` (`:132`) together
  with `‖0‖_{Ḣ^{1/2}} = 0`.  This is the field `RMainAPI.nonDensityZero`
  consumes at `q = 1`. -/
  inhomogeneousAtZero : ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (c * ν) →
        maximalLifespanR ν (fun _ : Space => (0 : Space)) f = ⊤
  /-- ⟪A02:exists_maximal⟫ (`research/A02/Spec.lean:421`,
  `02-preliminaries.tex:105`): for every admissible datum there is a maximal
  solution `(u,p)`, the field along which every a-priori estimate below is
  computed. -/
  existsMaximal : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
    ∀ f : SpaceTimeField, MemForceR f →
      ∃ u : SpaceTimeField, ∃ p : SpaceTimeScalar, IsMaximalSolution ν a f u p
  /-- ⟪A02:lifespan_le_iff_no_extension⟫ (`research/A02/Spec.lean:451`,
  `02-preliminaries.tex:32,105`): `T^ν_{max,R}(a,f) ≤ T` iff no classical
  solution reaches beyond `T`.  With `continuation` and
  `h2SquaredIntegralFinite` this is what turns "extends past every finite `S`"
  into `T^ν_{max,R} = ⊤` (`04-whole-space.tex:131`, "excludes every finite
  maximal lifespan").  `0 ≤ T` is needed because `ENNReal.ofReal` collapses the
  negative reals. -/
  lifespanLeIffNoExtension : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
      (T : ℝ), 0 ≤ T →
      (maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
        ∀ S : ℝ, T < S → IsEmpty (ClassicalSolutionR ν a f S))
  /-- ⟪A04:continuation (eq:criterion)⟫ (`02-preliminaries.tex:105-110`,
  `appendix-a-local-theory.tex:127-157`): the continuation criterion.  A
  classical solution on `[0,S)` whose squared-`H²` norm is time-integrable,
  `∫₀^S ‖u‖²_{H²} dt < ∞`, has `S` strictly below the maximal lifespan — it
  extends smoothly past `S`.  This is the clause A04 must export; A04 does not
  yet exist, so this is the first written shape of it
  (`research/R43/COMPARISON_A.md`).  The finiteness is stated on `w.velocity`
  of the *given* solution `w`, so `S` is never outside a genuine lifespan. -/
  continuation : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
    ∀ f : SpaceTimeField, MemForceR f → ∀ S : ℝ, 0 < S →
      ∀ w : ClassicalSolutionR ν a f S,
        (∫⁻ t in Ioo (0 : ℝ) S,
            sobolevENorm 2 (fun x : Space => w.velocity (t, x)) ^ 2 ∂volume) < ⊤ →
          ENNReal.ofReal S < maximalLifespanR ν a f
  /-- ⟪A05:velocityCriticalL3⟫ (`research/A05/Spec.lean:366`,
  `appendix-b-embeddings.tex:29`, `04-whole-space.tex:93`): the derived critical
  embedding `‖v‖₃ ≤ C‖v‖_{Ḣ^{1/2}}` on any `H^∞` field, the `a = 1/2` line of
  `eq:critical-derived`.  This is the clause that produces the `‖u‖₃` step; the
  companion clauses `derivativeCriticalL3` (`‖∇u‖₃ + ‖Λu‖₃ ≤ Cz`) and
  `gradientLSix` (`‖∇u‖₆ ≤ C‖Δu‖₂`) act inside `criticalNormBound` and inside
  C01's `eq:RH1` and are recorded in `research/R43/COMPARISON_A.md`. -/
  velocityCriticalL3 : ∀ v : SpatialField, MemHInfty v →
    eLpNorm v 3 volume ≤ ENNReal.ofReal Cemb * dotHomogeneousENorm (1 / 2) v
  /-- **Intermediate bound — the critical-norm bound** (`04-whole-space.tex:97-104`,
  `eq:Rcritical1`): along the maximal solution of small critical data, the
  homogeneous quantity `y(t) = ‖u(t)‖_{Ḣ^{1/2}}` stays below `c ν` throughout
  the lifespan.  This is the `y(t) ≤ y(0) + ∫₀^t b` bound after regularised norm
  division `(y²+ζ²)^{1/2}, ζ↓0` and the continuity bootstrap on `{y ≤ ν/(2C₀)}`,
  with `c < 1/(4C₀)` propagating it "throughout the lifespan by continuity,
  including at times where `y = 0`" (`:104`).  Scoped to the small-data regime,
  where it is what makes the nonlinearity absorbable. -/
  criticalNormBound : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
    ∀ f : SpaceTimeField, MemForceR f →
      dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
          < ENNReal.ofReal (c * ν) →
        ∀ u : SpaceTimeField, ∀ p : SpaceTimeScalar, IsMaximalSolution ν a f u p →
          ∀ t : ℝ, t ∈ presingularTimes ν a f →
            dotHomogeneousENorm (1 / 2) (fun x : Space => u (t, x))
              ≤ ENNReal.ofReal (c * ν)
  /-- **Intermediate bound — the `‖u‖₃` step** (`04-whole-space.tex:93,97-104`):
  the whole-space analogue of Proposition 4.4's `‖u‖₃ ≤ Cθν` step
  (`:157`).  Combining `velocityCriticalL3` (`‖u‖₃ ≤ Cemb·y`) with
  `criticalNormBound` (`y ≤ c ν`), the solution's `L³` norm stays below
  `Cemb·(c ν)` throughout the lifespan.  It is this `O(ν)` smallness of `‖u‖₃`
  that yields both `(ν − C₀y) ≥ ν/2` in `eq:Rcritical1` and `C₁y ≤ ν/4` in
  `eq:RH1`. -/
  velocityL3Small : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
    ∀ f : SpaceTimeField, MemForceR f →
      dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
          < ENNReal.ofReal (c * ν) →
        ∀ u : SpaceTimeField, ∀ p : SpaceTimeScalar, IsMaximalSolution ν a f u p →
          ∀ t : ℝ, t ∈ presingularTimes ν a f →
            eLpNorm (fun x : Space => u (t, x)) 3 volume
              ≤ ENNReal.ofReal (Cemb * (c * ν))
  /-- ⟪C01:h2TimeIntegral⟫ **— the `∫₀^S ‖u‖²_{H²}` bound**
  (`04-whole-space.tex:118-131`): C01's assembled estimate.  Along the maximal
  solution of small critical data, for every finite `S` **within or at** the
  maximal lifespan the squared-`H²` norm is time-integrable,
  `∫₀^S ‖u‖²_{H²} dt < ∞`.  C01 builds it from `eq:RL2`
  (`‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀^t ‖f‖₂ =: K(t)`), `eq:RH1`
  (`(‖∇u‖₂²)' + ν‖Δu‖₂² ≤ Cν⁻¹‖f‖₂²`, valid once `C₁‖u‖₃ ≤ ν/4`) and the `H²`
  Fourier inequality `‖u‖²_{H²} ≤ C(‖u‖₂² + ‖Δu‖₂²)`, giving the explicit bound
  `≤ C S K(S)² + Cν⁻¹‖∇a‖₂² + Cν⁻²∫₀^S‖f‖₂²` (`:127-130`); only its finiteness
  is consumed here, that being what `continuation` needs.  C01 does not yet
  exist, so this is the first written shape of the clause
  (`research/R43/COMPARISON_A.md`).  `ENNReal.ofReal S ≤ maximalLifespanR`
  encodes "within or at the maximal lifespan" (`:121`): `S` is never past it. -/
  h2SquaredIntegralFinite : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField,
    a ∈ initialClassR → ∀ f : SpaceTimeField, MemForceR f →
      dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
          < ENNReal.ofReal (c * ν) →
        ∀ u : SpaceTimeField, ∀ p : SpaceTimeScalar, IsMaximalSolution ν a f u p →
          ∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
            (∫⁻ t in Ioo (0 : ℝ) S,
                sobolevENorm 2 (fun x : Space => u (t, x)) ^ 2 ∂volume) < ⊤

end BlowupDensity.R43.DraftA
