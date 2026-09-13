import Contracts.V1.Data

/-!
# A01 draft specification: the whole-space local solution adapter

Task `collaboration/tasks/A01.md`, graph node `A01` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:172`.

This file is a **specification draft only**.  It contains `def`s and two
`structure`s; it proves nothing, assumes nothing, introduces no `axiom`, no
`sorry` and no abstract propositional variable.  Nothing here asserts that a
local solution exists: `LocalTheoryAPI` is a *record of obligations* whose
inhabitation is exactly what A01 has to supply.

## What A01 owns

`paper/sections/02-preliminaries.tex:105` `prop:local` (= `lem:Rlocal`) asserts
local existence, uniqueness and continuation.  A01 owns only the **existence**
half on `R³`, in the form the appendix derives it
(`paper/sections/appendix-a-local-theory.tex:60-107`) from
Tao 2013 Theorem 5.4(ii)–(iv):

* one **common** positive interval `[0,T₀)` valid for *every* Sobolev order
  (`appendix-a-local-theory.tex:66-67` "The higher-order bounds in part (ii)
  hold on the same local interval for every order");
* an *ordinary physical* velocity and pressure on `R³`, real valued and
  classically smooth on the closed-at-zero slab
  (`ClassicalSolutionR.velocity_smooth`, `pressure_smooth`);
* `C^j_tH^k_x` regularity for all `j,k`, with one-sided time derivatives at
  `t = 0` (`appendix-a-local-theory.tex:71-76`);
* the projected forced equation `eq:projected`
  (`02-preliminaries.tex:81`) with force `P f`
  (`appendix-a-local-theory.tex:76-77`);
* the pressure-gradient recovery `eq:Rpressure` (`02-preliminaries.tex:90`)
  together with the explicit radial potential (`02-preliminaries.tex:96-100`).

Deliberately **not** here, and named with their owners:

* uniqueness on a common interval and the identification of the maximal
  solution — **A02** (`appendix-a-local-theory.tex:115-125`,
  `research/section4/STATEMENTS.md:310`);
* the continuation criterion `eq:criterion` and the `∫₀^S‖u‖²_{H²}` restart —
  **A04** (`02-preliminaries.tex:108`,
  `appendix-a-local-theory.tex:127-157`; `eq:Rhigh` is `:132-137` and
  `eq:highcontinuation` is `:142-145`);
* the mild equation `eq:mild` (`appendix-a-local-theory.tex:109-114`).  It is
  the *bridge* used by A02's Grönwall uniqueness and by A04's restart, not a
  clause of `prop:local`; stating it here would force a heat-semigroup object
  into the existence contract.  `research/A01/COMPARISON.md` §2 records it as
  an adapter edge with its owner.
* the viscosity rescaling (`appendix-a-local-theory.tex:79-87`) and the
  periodic mean reduction (`:89-107`): both are *proof devices* of the
  appendix, and the whole-space statement quantifies over `ν > 0` directly.

## Conventions

Every object quantified over is the canonical one of
`verification/Contracts/V1/Data.lean` (`research/D01/PAPER_TO_LEAN.md`):
`initialClassR` is `X_R`, `MemForceR` is `F_R`, `ClassicalSolutionR` is the
classical solution on `[0,T)`, `PressureGaugeEquivOn` is the pressure gauge and
`pressurePotential` is the manuscript's radial potential.  Time is the first
spacetime coordinate.  Nothing in this file re-defines a D01 object.

Two objects D01 deliberately left out are defined here, because `prop:local` is
their first consumer (`research/D01/RECONCILIATION.md:173`, "Genuinely absent
objects" items 2 and 3):

* `convectionDivergence`, the manuscript's `∇·(u⊗u)`;
* `IsLerayComplement`, the Helmholtz characterization of `(I−P)`.

`IsLerayComplement` is a *characterization*, not the Fourier-symbol
construction of `02-preliminaries.tex:76`: `G` is the gradient part of `w` when
`G ∈ L²`, `G` has symmetric Jacobian (the manuscript's own consequence
`∂_jG_k = ∂_kG_j`, `02-preliminaries.tex:94`) and `w − G` is divergence free.
On `R³` this determines `G` uniquely — a difference of two such fields is
curl free, divergence free and `L²`, hence harmonic and zero — so no choice is
smuggled in.  Identifying it with the symbol `I − ξ⊗ξ/|ξ|²` is unit **P1** of
`research/A01/COMPARISON.md` §3, not a hypothesis of this contract.
-/

noncomputable section

namespace BlowupDensity.A01.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime coordinateVector
  temporalDerivative spatialLaplacian pressureGradient)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-! ## 1. Objects `prop:local` needs and `Data.lean` does not define -/

/-- `02-preliminaries.tex:81` eq:projected and `:90` eq:Rpressure, the tensor
divergence `∇·(u⊗u)`, whose `k`-th component is `∑_j ∂_j(u_ju_k)`.

Written literally as `∑_j ∂_j (u_j · u)`, a vector-valued spatial derivative at
frozen time.  For a divergence-free field this equals the upstream
`advection` `(u·∇)u` that `ClassicalSolutionR.momentum` uses; that identity is
unit **E1** of `research/A01/COMPARISON.md` §3, not a definitional shortcut.
Keeping the manuscript's own spelling is what makes `projected` below a
statement about `eq:projected` rather than a restatement of `momentum`. -/
def convectionDivergence (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  ∑ j : Fin 3,
    fderiv ℝ (fun y : Space => (u (t, y) j) • u (t, y)) x (coordinateVector j)

/-- `02-preliminaries.tex:94` "its Fourier transform is parallel to `ξ`.  Hence
`∂_jG_k = ∂_kG_j`": `G` is differentiable and its Jacobian is symmetric.  This
is exactly the hypothesis under which the manuscript's radial potential
differentiates back to `G` (`02-preliminaries.tex:96-100`).

`Differentiable ℝ G` is part of the predicate, not a side condition of its
consumers: Mathlib's `fderiv` returns junk `0` at a point of
non-differentiability, so without it *every* nowhere-differentiable field would
have a "symmetric Jacobian" and `IsLerayComplement` below would cease to be
single-valued (`research/A01/REVIEW.md` H2).  It costs nothing where the
predicate is used — `G = ∇p` and `ClassicalSolutionR.pressure_smooth` is
`ContDiffOn ℝ ∞`. -/
def HasSymmetricJacobian (G : SpatialField) : Prop :=
  Differentiable ℝ G ∧
    ∀ x : Space, ∀ i j : Fin 3,
      (fderiv ℝ G x (coordinateVector i)) j = (fderiv ℝ G x (coordinateVector j)) i

/-- `02-preliminaries.tex:76-90`: `G = (I−P)w`, the gradient part of the
Helmholtz decomposition of a spatial field `w`, characterized rather than
constructed.

Three clauses, each a manuscript sentence: `G ∈ L²`
(`02-preliminaries.tex:101` "Its gradient belongs to `L²`, so a nonzero
constant pressure gradient is excluded"), `G` differentiable and curl free
(`02-preliminaries.tex:94`), and `w − G = Pw` divergence free
(`02-preliminaries.tex:76-79`, the range of `P`).

Single-valuedness (unit **P2**) holds for **differentiable** `w`: two witnesses
differ by an `L²` field that is curl free and divergence free, hence harmonic
and zero.  `IsSolenoidal` also reads a bare `fderiv`, so the differentiability
of `w` is a hypothesis of that unit, not of this definition; on the class this
contract applies it to, `w = f − ∇·(u⊗u)` is smooth.

The complement is `Pw = w − G`, so `eq:projected`'s right-hand side
`P(f − ∇·(u⊗u))` is `(f − ∇·(u⊗u)) − G`; this is how `projected` below is
written, with no Leray operator as data. -/
def IsLerayComplement (w G : SpatialField) : Prop :=
  MemLp G 2 (volume : Measure Space) ∧
    HasSymmetricJacobian G ∧
    IsSolenoidal (fun x : Space => w x - G x)

/-! ## 2. The clauses of `prop:local` carried on top of `ClassicalSolutionR` -/

/-- The four clauses of `prop:local` that `ClassicalSolutionR` does **not**
already contain, imposed on a solution `u` of `ClassicalSolutionR ν a f T`.

`ClassicalSolutionR` (`Data.lean:617`) already carries: positivity of the
horizon; joint smoothness of velocity and pressure on `[0,T) × R³`, one-sided
at `t = 0`; `u(·,0) = a`; `∇·u = 0`; `eq:NS` at interior times in the
`(u·∇)u + ∇p` form; a *continuous* order-`m` datum path for every integer `m`;
and `∇p ∈ L²`.  What is added below is precisely the content that
`appendix-a-local-theory.tex:60-107` extracts beyond a classical solution:
Sobolev-valued *time smoothness* of every order, the projected form of the
equation, and the pressure recovery.

All four clauses are stated on the **one** horizon `T`.  That the order `m` is
quantified *inside* the fixed `T` is the appendix's "one common existence
interval for all Sobolev orders" (`02-preliminaries.tex:117`,
`appendix-a-local-theory.tex:66-67`); it is the reason a fixed-order witness does
not discharge this contract. -/
structure ManuscriptLocalRegularity (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (u : ClassicalSolutionR ν a f T) : Prop where
  /-- `appendix-a-local-theory.tex:71-76`: "repeated time differentiation gives
  `C^j_tH^k_x` regularity for all `j,k`, including one-sided derivatives at the
  initial time".  For every integer order `m` the velocity has an order-`m`
  angular datum at every time of `[0,T)`, and that datum path is `C^∞` in time
  on `[0,T)`.  `Ico 0 T` is `UniqueDiffOn`, so the derivative at `t = 0` is the
  one-sided one and no negative-time extension is differentiated — the same
  convention `MemForceR` uses on `futureTimes` (`Data.lean:537`).

  This strictly strengthens `ClassicalSolutionR.sobolev`, which asks only for
  `ContinuousOn`; the datum is unique (`research/D01/RECONCILIATION.md` unit
  L1), so the two paths coincide wherever both exist. -/
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t ∈ Ico (0 : ℝ) T,
        IsSobolevDatum (m : ℝ) (fun x : Space => u.velocity (t, x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)
  /-- `02-preliminaries.tex:90` eq:Rpressure,
  `∇p = (I−P)(f − ∇·(u⊗u)) =: G`: the pressure gradient of the solution *is*
  the Helmholtz gradient part of the forced convection residual, at every time
  of `[0,T)` including `t = 0`.

  Stated at `t = 0` as well as at interior times, because
  `02-preliminaries.tex:90` prescribes the pressure of a classical solution
  everywhere on its interval, while `ClassicalSolutionR.momentum` is imposed on
  `Ioo 0 T` only.  On `Ioo 0 T` this clause is D01 unit **L9(c)**
  (`research/D01/RECONCILIATION.md:160`, "eq:Rpressure ⟺ `momentum` given
  `divergence` and `∇p ∈ L²`"), so the genuine increment of this field is the
  `t = 0` endpoint; the redundancy is kept so that the manuscript's own
  prescription is readable in one place. -/
  pressure_recovery : ∀ t ∈ Ico (0 : ℝ) T,
    IsLerayComplement
      (fun x : Space => f (t, x) - convectionDivergence u.velocity t x)
      (fun x : Space => pressureGradient u.pressure t x)
  /-- `02-preliminaries.tex:81` eq:projected,
  `∂_tu − νΔu = −P∇·(u⊗u) + P f`, with the force `P f` of
  `appendix-a-local-theory.tex:76-77`.

  Written as `P(f − ∇·(u⊗u)) = (f − ∇·(u⊗u)) − ∇p`, which is what the previous
  clause makes it: by `pressure_recovery` the subtracted field is exactly the
  Leray complement of `f − ∇·(u⊗u)`, so this line and that one together are
  eq:projected, with no Leray operator appearing as data.

  Imposed at interior times, matching `ClassicalSolutionR.momentum`: the
  upstream `temporalDerivative` is a two-sided `fderiv` in time and need not
  exist at `t = 0` for a field smooth only on `[0,T) × R³`
  (`research/D01/RECONCILIATION.md` §1.6). -/
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x =
      (f (t, x) - convectionDivergence u.velocity t x) -
        pressureGradient u.pressure t x
  /-- `02-preliminaries.tex:96-100`: the scalar pressure may be taken to be the
  explicit radial potential `p(x,t) = ∫₀¹G(rx,t)·x dr` of its own gradient,
  the manuscript's chosen representative inside the gauge class.

  The solution's `pressure` is required to differ from that potential by a
  function of time only, which is exactly `02-preliminaries.tex:31` "the scalar
  pressure is determined up to a function of time".  Together with
  `pressure_recovery` this is the manuscript's full pressure prescription:
  the gradient is fixed by eq:Rpressure and the potential fixes the gauge. -/
  pressure_potential : PressureGaugeEquivOn (Ico (0 : ℝ) T)
    (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2))
    u.pressure

/-! ## 3. The contract -/

/-- **The existence half of `prop:local` on `R³`**
(`paper/sections/02-preliminaries.tex:105`, derived at
`paper/sections/appendix-a-local-theory.tex:60-107`).

For every viscosity `ν > 0`, every initial velocity `a ∈ X_R` and every force
`f ∈ F_R` there is a positive horizon `T₀(ν,a,f)` and a classical whole-space
solution on `[0,T₀)` with the manuscript's all-order Sobolev regularity, time
smoothness, projected forced equation and pressure recovery.

The horizon and the solution are **data**, not existential statements, so a
consumer can name `the` local solution.  This is what makes the contract usable
by A02, which must compare the constructed insertion field with *the* solution
for `(a,g)` and then identify the maximal one
(`research/section4/STATEMENTS.md:310,333`); by R43/R44, which invoke
`prop:local` at every finite candidate endpoint (`04-whole-space.tex:132`,
`STATEMENTS.md:549`); and by R45, which needs only `a ∈ X_R` so that the same
framework covers `a ∈ S_σ` (`STATEMENTS.md:706`).

**What this contract does *not* give R42.**  `RInsertAPI`
(`STATEMENTS.md:330-333`) needs a reference `(v,π)` that is a classical
solution on the *closed* interval `Icc 0 (T+δ)` together with
`referenceLifespan : T + δ < maximalLifespanR ν a g`.  `LocalTheoryAPI`
produces a solution only on `[0, horizon ν a g)`, and nothing here relates
`horizon` to `T + δ`: the horizon is a *local* interval, not a maximal one.
R42's reference is therefore supplied by its own `RegularThrough ν a g T`
hypothesis (`02-preliminaries.tex:34`, `Data.lean:657`) — which already
asserts a `ClassicalSolutionR ν a g (T+δ)` — with A02 identifying that
solution with the one below on the overlap and turning `RegularThrough` into
the strict lifespan inequality.  A01 supplies the *local piece* and the
uniqueness input; the `[0,T+δ]` statement is A02's.

No uniqueness clause appears: the solution field of this structure is *a*
witness, and its identification with every other classical solution of the same
data is A02's obligation.

No uniqueness clause appears: the solution field of this structure is *a*
witness, and its identification with every other classical solution of the same
Consequently `maximalLifespanR ν a f > 0` follows
from this contract alone (`Data.lean:650`, the supremum is over nonempty
horizons), which is the residual risk `research/D01/RECONCILIATION.md:243`
records as "provable-but-vacuous until prop:local lands".

This is a specification: every field is either data or a fully spelled-out
manuscript statement; no field is an abstract proposition variable. -/
structure LocalTheoryAPI where
  /-- `T₀ = T₀(ν,a,f) > 0`, the common existence horizon of
  `02-preliminaries.tex:117` "with one common existence interval for all
  Sobolev orders".  Total as a function so that no choice principle is needed
  to name it; its positivity is `(solution …).horizon_pos` and is not repeated
  as a field. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ
  /-- The classical solution itself, on `[0,T₀)`, for every manuscript datum:
  `ν > 0`, `a ∈ X_R = H^∞ ∩ L²_σ` (`02-preliminaries.tex:12` eq:Rinitial) and
  `f ∈ F_R` (`02-preliminaries.tex:17` eq:Rclasses).  Exposed as data, so that
  `velocity` and `pressure` below are functions of the datum.

  *Narrowing, recorded deliberately.*  `prop:local` itself asks only for "each
  force smooth into every `H^m` on compact time intervals"
  (`02-preliminaries.tex:107-108`); `MemForceR` additionally demands the
  `L¹_t`/`L²_t` finiteness of eq:Rclasses.  This contract is therefore stated
  on a strictly smaller force class than the proposition.  That is exactly the
  class Section 4 quantifies over — `F_c ⊆ F_rd ⊆ F_R`
  (`04-whole-space.tex:183-192`) — so nothing downstream is lost; a consumer
  needing the wider hypothesis must widen this field. -/
  solution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ClassicalSolutionR ν a f (horizon ν a f)
  /-- `paper/sections/appendix-a-local-theory.tex:66-77` together with
  `02-preliminaries.tex:81,90,96`: the four clauses of `prop:local` that go
  beyond `ClassicalSolutionR`, for that same solution on that same horizon —
  all-order Sobolev time smoothness, eq:Rpressure, eq:projected and the radial
  potential. -/
  regularity : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f),
      ManuscriptLocalRegularity ν a f (horizon ν a f) (solution ν a f hν ha hf)
  /-- `appendix-a-local-theory.tex:147-150`: "The `H¹` local existence bounds of
  the cited Theorems 5.1(ii) and 5.4(ii) then give **a common positive
  existence duration** when restarting at `t₀ ↑ S`: the initial `H¹` norms stay
  bounded, and `f` is bounded into `H¹` on `[0,S+1]`."

  The horizon is uniform over any `H¹` ball: for each `ν > 0` and each finite
  bound `K` on `‖a‖_{H¹}` and `‖f‖_{L¹_tH¹}` there is one `δ > 0` below every
  horizon in that ball.  Quantifier order is the operative content — `δ` is
  chosen *before* the datum, so a restart family with bounded `H¹` data gets one
  step length.

  *Why a field and not a remark.*  Without it `horizon` is an arbitrary total
  function and **A04 cannot state its restart from this contract**
  (`research/A01/REVIEW.md` M5): the continuation proof needs precisely the
  displayed uniformity, applied at `t₀ ↑ S`.  A01 is the only owner of a
  property of the local existence theorem.

  *Why qualitative and not a formula.*  Neither `prop:local`
  (`02-preliminaries.tex:105-115`) nor the appendix displays a lower bound for
  `T₀` in terms of `ν` and the norms; the quantitative source behind the
  appendix's sentence is Tao 2013 Theorem 5.4(ii), whose smallness condition is
  `(‖u₀‖_{H¹} + ‖f‖_{L¹_tH¹})⁴ T ≤ c` at viscosity one (published p. 52,
  eq. (46)), rescaled to `ν` by `appendix-a-local-theory.tex:79-87`.  This field
  states only what the manuscript asserts.  If A04 turns out to need the
  explicit `c`-form — for a quantitative restart rather than a merely uniform
  one — that is a strengthening of this field, not a new one.

  The `H¹` norms are the D01 quantities `sobolevENorm 1` (`Data.lean:189`) and
  `forceSobolevENormL1 1` (`Data.lean:231`), both `ℝ≥0∞`-valued and fail-safe to
  `⊤`, so `K ≠ ⊤` is the manuscript's "stay bounded". -/
  horizon_lower_bound : ∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField),
        a ∈ initialClassR → MemForceR f →
          sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K →
            δ ≤ horizon ν a f

/-! ## 4. Accessors for A02

Naming the fields of the chosen solution, so that downstream contracts refer to
`the` local velocity and pressure rather than re-deriving them.  These are the
*local* fields on `[0, horizon ν a f)`; R42's reference on `Icc 0 (T+δ)` is a
different object, see the note in `LocalTheoryAPI`. -/

/-- The local velocity `u` for the datum `(ν,a,f)`.  R42's reference field `v`
(`04-whole-space.tex:32` thm:Rinsert, `STATEMENTS.md:330-333`) *agrees* with
this on `[0, horizon ν a g)` but is defined on the longer `Icc 0 (T+δ)`; the
agreement and the extension are A02's, not this accessor's. -/
def LocalTheoryAPI.velocity (api : LocalTheoryAPI) {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) :
    SpaceTimeField :=
  (api.solution ν a f hν ha hf).velocity

/-- The local pressure `p` for the datum `(ν,a,f)`.  As for `velocity`, R42's
reference pressure `π` agrees with this only on `[0, horizon ν a g)` and up to
`PressureGaugeEquivOn`; the `[0,T+δ]` statement is A02's. -/
def LocalTheoryAPI.pressure (api : LocalTheoryAPI) {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) :
    SpaceTimeScalar :=
  (api.solution ν a f hν ha hf).pressure

/-- The common horizon of the chosen solution, as an extended real, so that it
can be compared with `maximalLifespanR` (`Data.lean:650`) without a coercion at
each use site.  A02 owns the inequality
`ENNReal.ofReal (api.horizon ν a f) ≤ maximalLifespanR ν a f`. -/
def LocalTheoryAPI.horizonENNReal (api : LocalTheoryAPI) (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) : ENNReal :=
  ENNReal.ofReal (api.horizon ν a f)

end BlowupDensity.A01.Draft
