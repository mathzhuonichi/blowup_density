import Contracts.V1.Data
import Contracts.V1.TameProduct
import Contracts.V1.BoundedRepresentative

/-!
# A04 draft specification: the squared-`H²` continuation adapter

Task `collaboration/tasks/A04.md`, graph node `A04` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:205` (`A04 ← A02, A03`; consumers
`A04 → R43`, `A04 → R44`).

This file is a **specification draft only**.  It contains `def`s and one
`structure`; it proves nothing, assumes nothing, introduces no `axiom`, no
`sorry` and no abstract propositional variable.  Every field is either data or a
fully spelled-out manuscript statement.

**Revision 2**, after [`REVIEW.md`](REVIEW.md) (verdict ACCEPT-WITH-NOTES).
Changed: the two statement defects in `lifespanInfiniteOfLocallyFinite` (the
criterion range, finding 1, and the missing lifespan positivity, finding 2); the
A03 contract is now imported rather than mirrored (finding 3); the
differentiability A01 supplies is an explicit hypothesis
(`HasSmoothSobolevPath`, finding 4); the redundancy of `MemL1Hm` and
`BoundedIntoHOne` is recorded at each use site (finding 5); and
`highContinuationIntegral` no longer rests on the interval-integral junk value
(finding 6).  `research/A04/ATTEMPTS.md` lists the changes.

## What A04 owns

`paper/sections/02-preliminaries.tex:105` `prop:local` (= `lem:Rlocal`) asserts
local existence, uniqueness and continuation.  A01 owns the existence half
(`research/A01/Spec.lean` `LocalTheoryAPI`), A02 owns uniqueness, patching and
the uniform restart step (`research/A02/Spec.lean` `MaximalSolutionAPI`).  A04
owns the **last third**: the displayed continuation criterion

  `∫₀^S ‖u(t)‖²_{H²(D)} dt < ∞  ⟹  the solution extends smoothly beyond S`
  (`02-preliminaries.tex:108-114` eq:criterion),

in the form the appendix proves it
(`paper/sections/appendix-a-local-theory.tex:127-157`):

* the all-order energy inequality **eq:Rhigh**
  (`appendix-a-local-theory.tex:132-137`),
  `½(‖u‖²_{H^m})' + ν‖∇u‖²_{H^m} ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}
   + ‖f‖_{H^m}‖u‖_{H^m}` for every integer `m ≥ 3`, with the pressure term gone
  by solenoidality and the nonlinearity bounded by eq:Rproduct/eq:tame;
* the `ζ`-regularization and Young step
  (`appendix-a-local-theory.tex:139-141`, "Young's inequality and division by
  the regularized norm `(‖u‖²_{H^m}+ζ²)^{1/2}`, followed by `ζ↓0`") producing
  **eq:highcontinuation** (`:142-145`),
  `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m}`;
* the Grönwall consequence (`:146-147`, "If eq:criterion holds, Grönwall bounds
  every `H^m` norm uniformly up to `S`");
* the restart (`:147-152`), "One interval extends beyond `S`, and uniqueness
  identifies it with the original solution on the overlap", and hence the
  criterion itself in the two shapes `prop:Rcritical1` and `prop:Rcritical2`
  consume (`04-whole-space.tex:129-134` and `:171`).

The manuscript's closing sentence `:155-157` — "This proves the asserted
continuation without requiring zero mean or a whole-space Poincaré inequality" —
is the reason **no spectral gap appears anywhere below**: the low frequencies are
carried by the `H^m` (inhomogeneous) norms throughout, and by `eq:RL2` on the
consumer side (C01), never by a Poincaré constant.

Deliberately **not** here, and named with their owners:

* local existence and the uniform horizon `T₀` on an `H¹` ball — **A01**
  (`research/A01/Spec.lean:283,297,338`; its unit **A2** is *this* Grönwall, see
  `research/A04/COMPARISON.md` §3);
* uniqueness, patching, and the quantitative restart at a presingular time
  `t₀ ↑ S` — **A02** (`research/A02/Spec.lean` `MaximalSolutionAPI.restart`,
  `.restart_datum`, `.restart_force`, `.uniqueness`).  `restartBeyond` below is
  A02's `restart` **cashed at the endpoint**, not a second copy of it; the
  `δ`-before-datum quantifier order is A02's and is reused verbatim rather than
  restated as a field.  `research/A04/COMPARISON.md` §3 records the sharing;
* the ordinary energy identity `eq:RL2`, the `H¹` absorption `eq:RH1` and the
  assembly of `∫₀^S‖u‖²_{H²} < ∞` itself — **C01**
  (`research/section4/STATEMENTS.md:494-500`, `:602-606`).  A04 **consumes** that
  integral as a hypothesis and never produces it;
* the mild equation `eq:mild` (`appendix-a-local-theory.tex:109-114`).  The
  appendix's continuation proof is the displayed **energy** computation, not a
  Duhamel contraction, so no heat semigroup appears below.

## How the inputs of the other lanes enter — and why asymmetrically

`REVIEW.md` finding 4 asks why `boundedRepresentative` is a field while the A01
and A02 inputs are not.  The rule actually applied, made explicit here, is
**importability**, not logical role:

* **A03's two contracts are registered Lean modules**
  (`verification/Contracts/V1/TameProduct.lean`,
  `verification/Contracts/V1/BoundedRepresentative.lean`, registered in
  `verification/contracts.json` as `A03.tame_products` and
  `A03.bounded_representative`).  They are imported and carried as the fields
  `tame` and `boundedRepresentative`, so an implementer of `ContinuationAPI` has
  them in hand.
* **A01's and A02's specifications live under `research/`**, which is not a Lean
  library and cannot be imported by a file checked with
  `cd verification && lake env lean ../research/A04/Spec.lean`.  Carrying
  `maximal : MaximalSolutionAPI` is therefore not available to this draft.  The
  two things those lanes supply are handled separately:
  * the **`C^∞`-in-time datum path** (A01's
    `ManuscriptLocalRegularity.sobolev_smooth`, `research/A01/Spec.lean:230`) is
    what makes "`r ↦ ‖u(r)‖²_{H^m}` is differentiable" true, and that *is*
    asserted by three fields below — so it is written out as the explicit
    hypothesis `HasSmoothSobolevPath`.  Those three fields are now self-contained;
  * the **restart** (A02's `restart`, `research/A02/Spec.lean:550`) is a proof
    input of `restartBeyond` and is *not* made a hypothesis: restating it would
    require mirroring `IsMaximalSolution`, `presingularTimes` and `timeShift`,
    which is exactly the duplication `DEPENDENCY_GRAPH.md:205-209` and
    `research/A04/COMPARISON.md` §3 tell this lane to avoid.  The same holds for
    A02's `uniqueness` behind `boundedRepresentative`'s second use.  A standalone
    implementer must import A02; `COMPARISON.md` §4 units **D1** and **R1** are
    the pointers.

The remaining three fields (`higherOrderBound`, `extendsBeyond`,
`lifespanInfiniteOfLocallyFinite`) carry **exactly the manuscript's own
hypotheses** and no regularity rider, because they are transcriptions of
`appendix-a-local-theory.tex:146-147` and `02-preliminaries.tex:108-114`; adding
one would make them weaker than `prop:local`.

## Conventions

Every object quantified over is the canonical one of
`verification/Contracts/V1/Data.lean` (`research/D01/PAPER_TO_LEAN.md`):
`initialClassR` is `X_R`, `MemForceR` is `F_R`, `ClassicalSolutionR ν a f T` is
the classical solution on `[0,T)`, `maximalLifespanR` is `T^ν_{max,R}`,
`sobolevENorm` is `‖·‖_{H^s}` and `forceSobolevENormL1` is `‖·‖_{L¹_tH^s_x}`.
`‖∇v‖_{H^s}` is the registered `TameProduct.gradientSobolevENorm`.  Time is the
first spacetime coordinate.  Nothing in this file re-defines a D01 or an A03
object.

## Why the norms are `ℝ≥0∞` except inside a derivative, and the two totality caveats

`Data.sobolevENorm` is `ℝ≥0∞`-valued and fail-safe to `⊤`
(`Contracts/V1/Data.lean:189`), which is what makes "`∫₀^S‖u‖²_{H²} < ∞`" and
"`sup_{t<S}‖u‖_{H^m} < ∞`" literal statements with no integrability side
condition.  A derivative, however, needs a real-valued function, so the three
differential fields run on `sobolevNormAt`, the `.toReal` of the same quantity.
That is not a weakening where it is used: every field it is applied to is a slice
of a `ClassicalSolutionR`, whose `sobolev` field (`Data.lean:643`) supplies an
order-`m` datum at every time of `Ico 0 T`, so the `ℝ≥0∞` value is finite and
`.toReal` is the honest norm.  Recovering that finiteness is unit **N1** of
`research/A04/COMPARISON.md` §4.

The second totalization is Mathlib's `∫ s in t₀..t, …`, which returns `0` when
the integrand is not interval integrable — so an inequality written against it is
generally *false* rather than vacuous.  `highContinuationIntegral` therefore
**asserts** `IntervalIntegrable` alongside the bound rather than dividing by the
junk value or assuming integrability away; on a classical solution the integrand
is continuous on a compact interval (unit **N1**), so the conjunct costs the
implementer nothing and spares every consumer a side condition
(`REVIEW.md` finding 6).  `squaredHTwoIntegral`, by contrast, is an `∫⁻` in
`ℝ≥0∞` and is total with no caveat at all.
-/

noncomputable section

namespace BlowupDensity.A04.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-! ## 1. Objects A04 needs and neither `Data.lean` nor the A03 contracts define

`‖∇v‖_{H^s}`, `‖u ⊗ v‖_{H^s}` and `MemHmVector` are **not** defined here: they
are `Contracts.V1.TameProduct.gradientSobolevENorm` (`TameProduct.lean:192`),
`.outerSobolevENorm` (`:182`) and `.MemHmVector` (`:141`), used through the
imported contract.  Revision 1 mirrored seven of them because that module was
not yet on `erenup/integration`; `REVIEW.md` finding 3 records that the mirrors
are now stale, and they are gone. -/

/-- `‖u(t)‖_{H^s}` along a spacetime field, as a **real** number: the `.toReal`
of `Data.sobolevENorm` on the time-`t` slice.

Used only inside the three differential fields, where a derivative forces a real
carrier.  On every field those statements are applied to — the velocity of a
`ClassicalSolutionR` and a force in `F_R` — the underlying `ℝ≥0∞` value is
finite (`ClassicalSolutionR.sobolev`, `MemForceR`), so this is the norm and not a
`⊤ ↦ 0` artefact; see the module docstring and unit **N1**. -/
def sobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm s (fun x : Space => u (t, x))).toReal

/-- `‖∇u(t)‖_{H^s}`, the real form of the registered
`Contracts.V1.TameProduct.gradientSobolevENorm` (`TameProduct.lean:192`,
`appendix-a-local-theory.tex:134`) on the time-`t` slice; the dissipation term of
eq:Rhigh.  Same finiteness remark as `sobolevNormAt`. -/
def gradientSobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (Contracts.V1.TameProduct.gradientSobolevENorm s
    (fun x : Space => u (t, x))).toReal

/-- `02-preliminaries.tex:111-113` eq:criterion, the left-hand side
`∫₀^S ‖u(t)‖²_{H²(D)} dt`, on the whole-space instance `D = R³`.

A lower Lebesgue integral in `ℝ≥0∞`, so the quantity is **total**: no
integrability hypothesis is needed to write it, and eq:criterion is literally
`squaredHTwoIntegral S u ≠ ⊤`.  The time interval is `(0,S)`; the endpoint value
at `S` is never used, matching `research/section4/STATEMENTS.md` §9 item 15
("the velocity is undefined at `T`"). -/
def squaredHTwoIntegral (S : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (fun x : Space => u (t, x)) ^ 2

/-- `02-preliminaries.tex:108` "If a solution is defined on `[0,S)`": the field
pair `(u,p)` is, literally, the velocity and pressure of a classical solution of
`(ν,a,f)` on **every** horizon strictly below `S`.

This is the hypothesis shape of `research/A02/Spec.lean`'s
`lifespan_le_of_unbounded` and `insertion_lifespan_eq`, reused unchanged so that
a consumer holding A02's maximal solution can feed it here without a conversion.
Literal equality of the fields, rather than agreement on the slab, is what makes
the predicate usable — `ClassicalSolutionR` constrains its `velocity` and
`pressure` only on `Ico 0 b ×ˢ univ`, so a solution whose slab restriction is `u`
can always be presented with `velocity = u`.

*Positivity is free from this predicate.*  At `0 < S` it produces a
`ClassicalSolutionR ν a f (S/2)`, hence `0 < maximalLifespanR ν a f`
(`Data.lean:657`, a supremum over horizons carrying a solution).  This is why the
three fields stated on `SolvesBelow` need no separate positivity clause, while
`lifespanInfiniteOfLocallyFinite`, whose family is indexed by the lifespan
itself, does — `REVIEW.md` finding 2. -/
def SolvesBelow (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∀ b : ℝ, 0 < b → b < S →
    ∃ w : ClassicalSolutionR ν a f b, w.velocity = u ∧ w.pressure = p

/-- ⟪A01:ManuscriptLocalRegularity.sobolev_smooth⟫
(`research/A01/Spec.lean:230`), `appendix-a-local-theory.tex:71-76`: "repeated
time differentiation gives `C^j_tH^k_x` regularity for all `j,k`, including
one-sided derivatives at the initial time".  For every integer order the field
has an order-`m` datum at every time of `[0,T)` and that datum path is `C^∞` in
time there.

**Why this is a hypothesis and not left implicit** (`REVIEW.md` finding 4).
`energyIdentityHigh`, `regularizedNormDerivative` and `highContinuationIntegral`
*assert* that `r ↦ ‖u(r)‖²_{H^m}` is differentiable; `ClassicalSolutionR.sobolev`
(`Data.lean:643`) gives only `ContinuousOn`, so without this clause those three
fields are not discharegable from `ContinuationAPI` together with `Data.lean`
alone.  A01's specification cannot be a field of this file — `research/` is not a
Lean library — so the clause is restated verbatim here and tagged.  It is a copy,
not a weakening.

`Ico 0 T` is `UniqueDiffOn`, so the derivative at `t = 0` is the one-sided one
and no negative-time extension is differentiated, the same convention
`MemForceR` uses on `futureTimes` (`Data.lean:544`). -/
def HasSmoothSobolevPath (T : ℝ) (u : SpaceTimeField) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t ∈ Ico (0 : ℝ) T,
        IsSobolevDatum (m : ℝ) (fun x : Space => u (t, x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)

/-- `02-preliminaries.tex:17` eq:Rclasses, the **`L¹_t H^m` clause alone**:
`‖f‖_{L¹(0,∞;H^m(R³))} < ∞` for every integer `m ≥ 0`.

This is the forcing hypothesis the continuation proof actually integrates —
`appendix-a-local-theory.tex:144-145`'s `+‖f‖_{H^m}` is carried through Grönwall
as its time integral.

*Redundant, deliberately* (`REVIEW.md` finding 5).  `MemForceR f`
(`Data.lean:544`) already carries `MemLp G 1 forceTimeMeasure` at every integer
order, which **is** this predicate, so a consumer holding `MemForceR` gets it for
free — that derivation is unit **F1** of `research/A04/COMPARISON.md` §4.  It is
nevertheless listed as a separate hypothesis wherever it is used, so that the
contract displays the manuscript's own hypothesis rather than the ambient
Section 4 class, and so that a reader can see which half of `F_R` each field
consumes; the `L²_t` half is never used by A04. -/
def MemL1Hm (f : SpaceTimeField) : Prop :=
  ∀ m : ℕ, forceSobolevENormL1 (m : ℝ) f ≠ ⊤

/-- `appendix-a-local-theory.tex:150-151`, "`f` is bounded into `H¹` on
`[0,S+1]`": the *bounded local `H¹` forcing* hypothesis of the restart, with the
bound named so that it can be the same `K` as the velocity's.

Deliberately a sup bound on a compact time interval and **not** a time-integral
norm: it is the hypothesis of the cited `H¹` local existence theorems
(Tao 5.1(ii)/5.4(ii)) at each restart time, and the manuscript states it in
exactly this form.

*Redundant, deliberately*, for the same reason as `MemL1Hm` (`REVIEW.md`
finding 5): `MemForceR f` gives `ContDiffOn ℝ ∞ G futureTimes` at order one
(`Data.lean:544`), hence a finite bound on any compact `I ⊆ [0,∞)`.  That
derivation is the second half of unit **F1**.  It is listed explicitly because
`restartBeyond` needs the bound to be *the same* `K` that controls the velocity,
which the derivation alone does not deliver. -/
def BoundedIntoHOne (I : Set ℝ) (K : ℝ≥0∞) (f : SpaceTimeField) : Prop :=
  ∀ t ∈ I, sobolevENorm 1 (fun x : Space => f (t, x)) ≤ K

/-! ## 2. The contract

All constants are structure fields, hence quantified **outside** every viscosity,
datum, force, solution, order and time, as `appendix-a-local-theory.tex:10`
requires of Lemma A.1's constants and as eq:Rhigh's `C_m` and
eq:highcontinuation's `C_{m,ν}` require of themselves. -/

/-- **The continuation half of `prop:local` on `R³`**
(`paper/sections/02-preliminaries.tex:105-114`, derived at
`paper/sections/appendix-a-local-theory.tex:127-157`), in the form
`prop:Rcritical1` and `prop:Rcritical2` consume it.

**What each consumer takes** (`research/section4/STATEMENTS.md:498-500`,
`:606-608`):

* `R43` (Proposition 4.3) takes `lifespanInfiniteOfLocallyFinite`: having bounded
  `∫₀^S‖u‖²_{H²}` for every finite `S` **within or at the maximal lifespan**,
  "Proposition 2.1 excludes every finite maximal lifespan"
  (`04-whole-space.tex:121`, `:132-133`).
* `R44` (Proposition 4.4) takes `extendsBeyond` at the prescribed `S`: the
  `L²`/`H¹` estimates "exclude a maximal lifespan at or before `S`"
  (`04-whole-space.tex:171`).
* Both reach those through `higherOrderBound` and `restartBeyond` only if they
  want the intermediate quantities; the two criterion fields are self-contained.

**What it takes from its DAG children.**  `A04 ← A02, A03`
(`DEPENDENCY_GRAPH.md:205-209`).  From A03 the two registered contracts, carried
as the fields `tame` and `boundedRepresentative`; from A02 the uniform restart,
which is *used* by `restartBeyond` and deliberately **not** restated as a field.
The module docstring section "How the inputs of the other lanes enter" explains
the asymmetry.

This is a specification: every field is either data or a fully spelled-out
manuscript statement; no field is an abstract proposition variable. -/
structure ContinuationAPI where
  /-- `appendix-a-local-theory.tex:132-137` eq:Rhigh, the constant `C_m`.
  It depends on the order **only** — not on `ν`, not on the field, not on the
  solution — because it arises from eq:tame's `C_k`
  (`appendix-a-local-theory.tex:17-18`) entering through the single
  Cauchy–Schwarz step `|⟨∇·(u⊗u),u⟩_{H^m}| ≤ ‖u⊗u‖_{H^m}‖∇u‖_{H^m}`.

  *Relation to `tame.Ctame`, decided explicitly* (`REVIEW.md` finding 3,
  sub-note).  Carrying out that step contributes a factor one, so an
  implementation **may** take `Chigh m = tame.Ctame m`.  The contract does not
  require it: `appendix-a-local-theory.tex:131` says only "using eq:Rproduct
  gives", and pinning the two together would oblige an implementer to prove a
  sharper identity than the manuscript states, for no gain — `R43` and `R44` use
  the criterion qualitatively and never see either constant.  Hence `Chigh` stays
  an opaque field of its own and `energyIdentityHigh` is stated with it.
  `research/A04/COMPARISON.md` §2 records the decision. -/
  Chigh : ℕ → ℝ
  /-- Positivity, which is what makes eq:Rhigh a bound and not a vanishing
  statement. -/
  Chigh_pos : ∀ m : ℕ, 0 < Chigh m
  /-- `appendix-a-local-theory.tex:142-145` eq:highcontinuation, the constant
  `C_{m,ν}`.  Its two arguments are the manuscript's own two subscripts: the
  order, inherited from `Chigh`, and the viscosity, which enters when Young's
  inequality absorbs `C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` into the dissipation
  `ν‖∇u‖²_{H^m}` at `:139-140`.

  *The manuscript displays no formula*, so none is pinned here; the derivation
  that produced it gives `C_{m,ν} = (C_m)²/(4ν)`, which any implementation may
  use and which `research/A04/COMPARISON.md` §2 records.  A consumer that needs
  the explicit `ν^{-1}` scaling — none in Section 4 does — must strengthen this
  field, not add one. -/
  Cgron : ℕ → ℝ → ℝ
  /-- Positivity at every positive viscosity. -/
  Cgron_pos : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < Cgron m ν
  /-- ⟪A03:TameProductAPI⟫, the registered contract
  `verification/Contracts/V1/TameProduct.lean:215`
  (`verification/contracts.json`, `A03.tame_products`).

  **The clause A04 consumes is `tame.outerProductTame`**
  (`TameProduct.lean:345`), `appendix-a-local-theory.tex:17-18` eq:tame:
  `‖u ⊗ u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` for integers `k ≥ 3`.  eq:Rhigh
  (`:132-137`) pairs the equation with `u` in `H^m`, integrates the nonlinear
  divergence by parts and bounds
  `|⟨∇·(u⊗u),u⟩_{H^m}| ≤ ‖u⊗u‖_{H^m}‖∇u‖_{H^m}`; only the first factor is Lemma
  A.1's, and it is exactly that clause.  The rest of `TameProductAPI`
  (`tameProductScalar`, `algebraProductScalar`, `outerProductDifference`,
  `smoothJets_advectionTame`) is A01's and A02's, not A04's.

  Carried whole rather than as the single clause, so that the contract names the
  registered object and an implementer needs no projection lemma.  Revision 1
  restated the clause and seven supporting definitions because this module was
  not yet on `erenup/integration`; `REVIEW.md` finding 3 records that they were
  symbol-for-symbol identical and are now deleted. -/
  tame : Contracts.V1.TameProduct.TameProductAPI
  /-- ⟪A03:BoundedRepresentativeAPI⟫, the registered contract
  `verification/Contracts/V1/BoundedRepresentative.lean:173`
  (`verification/contracts.json`, `A03.bounded_representative`),
  `‖v‖_∞ ≤ C‖v‖_{H²}` — the second clause of eq:Rproduct
  (`appendix-a-local-theory.tex:12`).

  Carried as a field for the same reason as `tame`: it is a registered, and
  therefore importable, contract.  Two places use it, both named in the
  manuscript.  (i) `appendix-a-local-theory.tex:131` cites eq:Rproduct as a whole
  for eq:Rhigh, and the embedding is the clause the product bound rests on.
  (ii) The restart's closing step, "uniqueness identifies it with the original
  solution on the overlap" (`:151-152`), is A02's uniqueness, whose Grönwall
  coefficient `‖∇u₂‖_∞` (`:118-123`) is bounded only through this clause
  (`research/A02/Spec.lean` header, `research/A02/COMPARISON.md` §5).

  No field below mentions an `L^∞` norm: A04 never states a blowup, it states a
  lifespan.  Converting the criterion into `limsup_{t↑T}‖u‖_∞ = ∞` is
  `04-whole-space.tex:53`, owned by R42 through A02. -/
  boundedRepresentative : Contracts.V1.BoundedRep.BoundedRepresentativeAPI
  /-- **eq:Rhigh** (`appendix-a-local-theory.tex:132-137`), the all-order energy
  inequality, on a compact interval of smooth existence (`:138-139`, "These
  identities are justified by Fourier approximation on compact intervals of
  smooth existence"):

  `½ (d/dt)‖u‖²_{H^m} + ν‖∇u‖²_{H^m}
      ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}`,

  for every integer `m ≥ 3` (`:129`) and every interior time of the solution's
  horizon.  "The pressure term vanishes by solenoidality" (`:137-138`) is
  discharged inside the proof by `ClassicalSolutionR.divergence`, and is why no
  pressure appears on either side.

  *Shape.*  `∃ d, HasDerivAt (fun r => ‖u(r)‖²_{H^m}) d t ∧ …` is "the squared
  norm is differentiable at `t` and its derivative obeys the bound".  The
  **squared** norm is used here, not the norm: on an inner-product carrier
  `r ↦ ‖G r‖²` is differentiable wherever the datum path is, with no
  regularization, whereas `r ↦ ‖G r‖` is not differentiable at a zero of `G` —
  which is exactly the defect the next field's `ζ` repairs.

  *`HasSmoothSobolevPath` is the differentiability input* (`REVIEW.md`
  finding 4): `ClassicalSolutionR.sobolev` gives only a continuous datum path,
  and the `C^∞`-in-time path is A01's clause, restated in §1.

  *Force.*  `MemForceR f` is the hypothesis, not `MemL1Hm f`: this line is
  pointwise in time and needs the manuscript's "`f` smooth into every `H^m`"
  (`02-preliminaries.tex:107-108`), not a time integral.  The `L¹_t` clause
  enters two fields below. -/
  energyIdentityHigh : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
        ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ d : ℝ,
            HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
              (1 / 2) * d + ν * gradientSobolevNormAt (m : ℝ) w.velocity t ^ 2 ≤
                Chigh m * sobolevNormAt 2 w.velocity t *
                    sobolevNormAt (m : ℝ) w.velocity t *
                    gradientSobolevNormAt (m : ℝ) w.velocity t +
                  sobolevNormAt (m : ℝ) f t * sobolevNormAt (m : ℝ) w.velocity t
  /-- **eq:highcontinuation before the limit**
  (`appendix-a-local-theory.tex:139-145`): "Young's inequality and division by
  the regularized norm `(‖u‖²_{H^m}+ζ²)^{1/2}`, followed by `ζ↓0`, imply
  `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m}`."

  This field is the statement **at each fixed `ζ > 0`**, which is the only form
  in which the manuscript's sentence is a theorem about a differentiable
  function:

  `(d/dt)(‖u‖²_{H^m}+ζ²)^{1/2}
     ≤ C_{m,ν}‖u‖²_{H²}(‖u‖²_{H^m}+ζ²)^{1/2} + ‖f‖_{H^m}`.

  Two things happen between this and the previous field and both are recorded
  here rather than hidden: Young's inequality absorbs the dissipation, turning
  `C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` into
  `ν‖∇u‖²_{H^m} + C_{m,ν}‖u‖²_{H²}‖u‖²_{H^m}` and introducing the `ν`-dependence
  of `Cgron`; and the division by the regularized norm replaces `‖f‖_{H^m}‖u‖`
  by `‖f‖_{H^m}` at the cost of the `ζ`, since
  `‖u‖_{H^m} ≤ (‖u‖²_{H^m}+ζ²)^{1/2}`.

  The same `ζ`-device appears twice more in the manuscript on the `L²` carrier
  (`02-preliminaries.tex:152` for the packet energy, `04-whole-space.tex:103` and
  `:121` for eq:RL2 and eq:Rcritical1), so an implementation should factor it;
  `research/A04/COMPARISON.md` §4 unit **Z1** books it once. -/
  regularizedNormDerivative :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T, ∀ ζ : ℝ, 0 < ζ →
            ∃ d : ℝ,
              HasDerivAt
                  (fun r : ℝ =>
                    Real.sqrt (sobolevNormAt (m : ℝ) w.velocity r ^ 2 + ζ ^ 2)) d t ∧
                d ≤ Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 *
                      Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2 + ζ ^ 2) +
                    sobolevNormAt (m : ℝ) f t
  /-- **eq:highcontinuation after `ζ↓0`** (`appendix-a-local-theory.tex:141-145`),
  in its integrated form on `[t₀,t] ⊆ [0,T)`:

  `‖u(t)‖_{H^m} ≤ ‖u(t₀)‖_{H^m}
     + ∫_{t₀}^{t}(C_{m,ν}‖u(s)‖²_{H²}‖u(s)‖_{H^m} + ‖f(s)‖_{H^m}) ds`.

  *Why integrated and not differential.*  After `ζ↓0` the left-hand side of
  eq:highcontinuation is `‖u‖_{H^m}`, which need not be differentiable at a time
  where `u` vanishes in `H^m`; the manuscript's `(‖u‖_{H^m})'` is shorthand for
  the inequality that survives the limit, and that inequality is this one.  It is
  also the only form Grönwall consumes, so nothing is lost.

  *The `IntervalIntegrable` conjunct* (`REVIEW.md` finding 6).  Mathlib's
  `∫ s in t₀..t, ·` is `0` on a non-integrable integrand, so an inequality
  written against it would be *false* rather than vacuous unless integrability is
  settled.  It is settled here by **asserting** it, not by assuming it: on a
  classical solution the integrand is continuous on a compact interval (unit
  **N1**), so the implementer pays nothing and every consumer is spared a side
  condition.  See the module docstring's second totality caveat.

  This is the field that carries the `L¹_t H^m` forcing: the integral of
  `‖f‖_{H^m}` over `[t₀,t]` is bounded by `‖f‖_{L¹_tH^m}`, finite by `MemL1Hm`
  (free from `MemForceR`, unit **F1**). -/
  highContinuationIntegral :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t₀ t : ℝ, 0 ≤ t₀ → t₀ ≤ t → t < T →
            IntervalIntegrable
                (fun s : ℝ =>
                  Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                      sobolevNormAt (m : ℝ) w.velocity s +
                    sobolevNormAt (m : ℝ) f s)
                volume t₀ t ∧
              sobolevNormAt (m : ℝ) w.velocity t ≤
                sobolevNormAt (m : ℝ) w.velocity t₀ +
                  ∫ s in t₀..t,
                    (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                        sobolevNormAt (m : ℝ) w.velocity s +
                      sobolevNormAt (m : ℝ) f s)
  /-- **The Grönwall consequence** (`appendix-a-local-theory.tex:146-147`): "If
  eq:criterion holds, Grönwall bounds every `H^m` norm uniformly up to `S`."

  Hypotheses: a classical solution on `[0,S)` in the manuscript's sense
  (`02-preliminaries.tex:108`, here `SolvesBelow`), the criterion
  `∫₀^S‖u‖²_{H²} dt < ∞` (eq:criterion, `:111-113`), and `L¹_t H^m` forcing
  (free from `MemForceR`, unit **F1**).  Conclusion: for **every** integer order a
  single finite bound valid on all of `[0,S)`.

  *No regularity rider.*  These are exactly the manuscript's hypotheses; A01's
  `HasSmoothSobolevPath` is a *proof* input here — it enters through the three
  differential fields above, which already carry it — and adding it as a
  hypothesis would make this field weaker than `appendix-a-local-theory.tex:147`.

  *Why every `m : ℕ` and not every `m ≥ 3`.*  The manuscript says "every `H^m`
  norm", and the orders `m ≤ 2` are the ones the restart actually uses — the
  `H¹` bound of `:149-150`.  Deducing them from the `m = 3` case is Sobolev
  monotonicity, unit **M1**; stating them here keeps the consumer from needing
  that unit.

  *Why `ℝ≥0∞` and not a real bound.*  `M ≠ ⊤` is the manuscript's "uniformly
  bounded" with no side condition, and it is the shape A02's `restart` consumes
  its `K` in (`research/A02/Spec.lean:550`). -/
  higherOrderBound : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
          ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
            ∀ t ∈ Ico (0 : ℝ) S,
              sobolevENorm (m : ℝ) (fun x : Space => u (t, x)) ≤ M
  /-- **The uniform restart past the endpoint**
  (`appendix-a-local-theory.tex:147-152`): "The `H¹` local existence bounds of
  the cited Theorems 5.1(ii) and 5.4(ii) then give a common positive existence
  duration when restarting at `t₀ ↑ S`: the initial `H¹` norms stay bounded, and
  `f` is bounded into `H¹` on `[0,S+1]`. … One interval extends beyond `S`, and
  uniqueness identifies it with the original solution on the overlap."

  For each viscosity and each finite `H¹` bound `K` there is one step `δ > 0`
  such that every endpoint `S` whose solution and force obey `K` has lifespan at
  least `S + δ`.  **The quantifier order is the whole content**: `δ` is chosen
  before `S`, before the datum and before the force, which is what lets the
  restart times `t₀ ↑ S` overshoot `S` instead of shrinking to zero.

  *This is A02's `restart` cashed at the endpoint, not a second copy of it.*
  `research/A02/Spec.lean:550` gives, with the same `δ(ν,K)`,
  `ofReal (t₀+δ) ≤ T^ν_{max,R}` at every presingular `t₀` with `K`-bounded datum
  and shifted force; A04's increment is the passage `t₀ ↑ S`, which needs the
  uniformity of the `H¹` bound over the *whole* of `[0,S)` — and that is what
  `higherOrderBound` at `m = 1` supplies.  `DEPENDENCY_GRAPH.md:205-209` records
  the edge; `research/A04/COMPARISON.md` §3 records why no A02 field is restated,
  and the module docstring why A02 cannot be a field of this file.

  *The three force conditions are the manuscript's own.*
  `BoundedIntoHOne (Icc 0 (S+1)) K f` is `:150-151` verbatim (the bounded local
  `H¹` forcing; the *existence* of some finite bound is free from `MemForceR`,
  unit **F1**, but its equality with the velocity's `K` is not);
  `forceSobolevENormL1 1 f ≤ K` is the `L¹_tH¹` half of the smallness condition
  behind Theorems 5.1(ii)/5.4(ii), and is the norm A01's `horizon_lower_bound` is
  stated in (`research/A01/Spec.lean:338`); `MemForceR` is the ambient class.
  All three are measured against the same `K`, so a consumer supplies one bound.

  *Positivity of the lifespan* is free from `SolvesBelow` at `0 < S`; see that
  definition's docstring. -/
  restartBeyond : ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
        (u : SpaceTimeField) (p : SpaceTimeScalar),
        a ∈ initialClassR → MemForceR f → 0 < S → SolvesBelow ν a f S u p →
          (∀ t ∈ Ico (0 : ℝ) S,
              sobolevENorm 1 (fun x : Space => u (t, x)) ≤ K) →
            BoundedIntoHOne (Icc (0 : ℝ) (S + 1)) K f →
            forceSobolevENormL1 1 f ≤ K →
              ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f
  /-- **The continuation criterion itself**, `02-preliminaries.tex:108-114`
  eq:criterion: "If a solution is defined on `[0,S)`, `S < ∞`, and
  `∫₀^S‖u(t)‖²_{H²(D)}dt < ∞`, then it extends smoothly beyond `S`."

  Extension beyond `S` is `ofReal S < T^ν_{max,R}(a,f)`: `maximalLifespanR`
  (`Data.lean:657`) is the supremum of horizons carrying a classical solution, so
  a strict inequality is exactly a solution on some `[0,S')` with `S' > S`, and
  A02's `uniqueness` makes it *the* solution.

  **This is the field `prop:Rcritical2` uses** (`04-whole-space.tex:171`, "the
  last continuation calculation in Proposition 4.3 exclude[s] a maximal lifespan
  at or before `S`"), with `S` the prescribed interval endpoint.

  *The contrapositive.*  Contraposing in the second hypothesis gives
  `maximalLifespanR ν a f ≤ ENNReal.ofReal S → squaredHTwoIntegral S u = ⊤`,
  which is the shape `04-whole-space.tex:53` and R42 argue in.  It is not a
  separate field: `maximalLifespanR ν a f ≤ ofReal S` contradicts
  `ofReal S < maximalLifespanR ν a f` directly, with `SolvesBelow` still
  available because every `b < S` is below the lifespan.

  *Hypotheses are exactly `prop:local`'s* — `SolvesBelow` and the criterion, with
  `MemL1Hm` free from `MemForceR` (unit **F1**); no regularity rider, for the
  reason given on `higherOrderBound`.  Lifespan positivity is free from
  `SolvesBelow` at `0 < S`.

  *No spectral gap.*  Neither hypothesis nor conclusion mentions a Poincaré
  constant or a mean-zero reduction; `appendix-a-local-theory.tex:155-157` is
  explicit that the whole-space statement needs neither, and the low frequencies
  are carried by the inhomogeneous `H²` norm inside `squaredHTwoIntegral`. -/
  extendsBeyond : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
          ENNReal.ofReal S < maximalLifespanR ν a f
  /-- **The criterion in `prop:Rcritical1`'s packaging**
  (`04-whole-space.tex:121`, `:132-133`): "For every finite `S` **within or at
  the maximal lifespan**, `K(S) < ∞`, and … `∫₀^S‖u(t)‖²_{H²}dt < ∞`.
  Proposition 2.1 **excludes every finite maximal lifespan**."

  Hypotheses: the lifespan is positive; `(u,p)` is the solution on every horizon
  strictly below it (`02-preliminaries.tex:32`, the `presingularTimes` family of
  `research/A02/Spec.lean:146`, written out so that no A02 definition is
  duplicated); and the squared-`H²` integral is finite at every finite endpoint
  **within or at the lifespan**.  Conclusion: `T^ν_{max,R}(a,f) = ∞`, which is
  how `prop:Rcritical1` states global regularity.

  *Two corrections from `REVIEW.md`, both load-bearing.*

  (1) **The criterion range** (finding 1).  Revision 1 asked for
  `∀ S, 0 < S → squaredHTwoIntegral S u ≠ ⊤`, over *all* `S`.  Past a
  hypothetical finite lifespan `T` the field `u` is unconstrained — neither this
  field's family nor `research/A02/Spec.lean:210` `IsMaximalSolution` pins it on
  `[T,∞)` — and `sobolevENorm` is fail-safe to `⊤` there, so C01's assembly
  (`04-whole-space.tex:122-128`) could not discharge the hypothesis at exactly
  the `S` this field exists to rule out.  The guard
  `ENNReal.ofReal S ≤ maximalLifespanR ν a f` is the manuscript's own range and
  costs the derivation nothing: contradiction at a finite supremum instantiates
  the hypothesis only at `S = T^ν_{max,R}`, where the guard holds with equality.

  (2) **Lifespan positivity** (finding 2).  The family clause is
  `IsMaximalSolution`'s second clause (`research/A02/Spec.lean:212-215`) and
  needs its first, `0 < maximalLifespanR ν a f`, for the same reason A02 gives
  (`:180-183`): the empty supremum of `maximalLifespanR` is `0`, so at a datum
  carrying no solution the family is vacuously true of `u = p = 0`, the integral
  is `0 ≠ ⊤` at every `S`, and the conclusion would assert `0 = ⊤`.  With the
  clause the field is self-contained and does not rest silently on A01's
  existence half.  The three fields above are stated on `SolvesBelow`, which
  produces positivity at `0 < S` on its own, so only this field needed it.

  Derivable from `extendsBeyond` by contradiction at a finite supremum; kept as a
  field because it is the literal step R43 performs and because the reduction
  needs the solution family at the endpoint, which is bookkeeping a consumer
  should not have to redo (`research/section4/STATEMENTS.md:498-500`). -/
  lifespanInfiniteOfLocallyFinite : ∀ (ν : ℝ) (a : SpatialField)
      (f : SpaceTimeField), 0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      0 < maximalLifespanR ν a f →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        (∀ b : ℝ, 0 < b → ENNReal.ofReal b < maximalLifespanR ν a f →
            ∃ w : ClassicalSolutionR ν a f b, w.velocity = u ∧ w.pressure = p) →
          (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
              squaredHTwoIntegral S u ≠ ⊤) →
            maximalLifespanR ν a f = ⊤

end BlowupDensity.A04.Draft
