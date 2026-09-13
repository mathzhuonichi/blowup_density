import Contracts.V1.Data

/-!
# A02 draft specification: uniqueness and maximal solution identification

Task `collaboration/tasks/A02.md`, graph node `A02` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:184` (`A02 ← A01`; consumers
`A02 → A04`, `A02 → C01`, `A02 → R42`).

This file is a **specification draft only**.  It contains `def`s and two
`structure`s; it proves nothing, assumes nothing, introduces no `axiom`, no
`sorry` and no abstract propositional variable.  Every field is either data or
a fully spelled-out manuscript statement.

## What A02 owns

`paper/sections/02-preliminaries.tex:105` `prop:local` (= `lem:Rlocal`) asserts
local existence, uniqueness and continuation.  A01 owns the **existence** half
(`research/A01/Spec.lean`), A04 owns the continuation criterion `eq:criterion`.
A02 owns the middle third, in the form the appendix derives it
(`paper/sections/appendix-a-local-theory.tex:115-125`):

* **uniqueness** — "if `z = u₁ − u₂` for two such solutions with the same data,
  `½(‖z‖₂²)' + ν‖∇z‖₂² ≤ ‖∇u₂‖_∞‖z‖₂²`.  The coefficient is bounded on compact
  common intervals, since `u₂ ∈ C_tH³`.  Grönwall gives uniqueness."
  (`appendix-a-local-theory.tex:119-124`);
* **patching and the maximal lifespan** — "Patching these local solutions
  defines the maximal lifespan" (`appendix-a-local-theory.tex:124-125`), which
  is the sentence `02-preliminaries.tex:32` turns into the *definition* of
  `T^ν_{max,R}(a,f)` (`Data.lean` `maximalLifespanR`);
* **the quantitative restart** — "The `H¹` local existence bounds … give a
  common positive existence duration when restarting at `t₀ ↑ S` … One interval
  extends beyond `S`, and uniqueness identifies it with the original solution
  on the overlap" (`appendix-a-local-theory.tex:147-152`).  A01 exports the
  uniform step as `LocalTheoryAPI.horizon_lower_bound`; A02 turns it into a
  statement about `maximalLifespanR` at an interior restart time;
* **the identification used by Theorem 4.2** — "Proposition 2.1 identifies the
  solution with the unique maximal solution.  An extension through `T` would be
  bounded in `C_tH²` on a neighbourhood of `T` … Thus its maximal lifespan is
  exactly `T`" (`04-whole-space.tex:53`).

Deliberately **not** here, and named with their owners:

* local existence itself — **A01** (`research/A01/Spec.lean` `LocalTheoryAPI`);
* the continuation criterion `eq:criterion` `∫₀^S‖u‖²_{H²} < ∞ ⟹ extension` —
  **A04** (`02-preliminaries.tex:108`, `appendix-a-local-theory.tex:127-157`).
  `lifespan_le_of_unbounded` below is its *contrapositive at the `H²` level*
  only for a solution whose `H²` norm is unbounded at `T`; it uses no time
  integral and no Grönwall in `m`, and does not discharge A04;
* the mild equation `eq:mild` (`appendix-a-local-theory.tex:109-114`).  The
  manuscript's uniqueness proof is the displayed **energy** estimate, not a
  Duhamel contraction, so no heat semigroup appears in this contract.
  `research/A01/COMPARISON.md` §2 edge **M** records `eq:mild` as owned by
  "A02/A04"; A02's *statement* does not need it, and the route recommendation in
  `research/A02/COMPARISON.md` §4 explains when an implementation would;
* the embedding `‖z‖_∞ ≤ C‖z‖_{H²}` of `eq:Rproduct`
  (`appendix-a-local-theory.tex:9-13`) — **A03**.  It is *used* twice below and
  *stated* nowhere: once to bound the Grönwall coefficient `‖∇u₂‖_∞` of
  `appendix-a-local-theory.tex:121-123`, and once in "an extension through `T`
  would be bounded in `C_tH²` … hence bounded in `L^∞`"
  (`04-whole-space.tex:53`).  The first of these is inside the *uniqueness*
  proof, so **A02 needs `A03` whatever shape its blow-up hypothesis takes**;
  today's DAG has `A02 ← A01` only.  `research/A02/COMPARISON.md` §5 records the
  recommended new edge `A03 → A02` (no cycle: `A03 ← D01, U04, A05`, none of
  which descends from `A02`).  Because that edge is needed regardless, the
  blow-up hypotheses below are written in the manuscript's own `L^∞` norm
  (`04-whole-space.tex:35`), which is also the literal shape of R42's `blowup`
  field (`research/section4/STATEMENTS.md:348-351`), rather than pushed onto
  R42 as an `H²` conversion.

## Conventions

Every object quantified over is the canonical one of
`verification/Contracts/V1/Data.lean` (`research/D01/PAPER_TO_LEAN.md`):
`initialClassR` is `X_R`, `MemForceR` is `F_R`, `ClassicalSolutionR ν a f T` is
the classical solution on `[0,T)`, `maximalLifespanR` is `T^ν_{max,R}`,
`RegularThrough` is "regular through `T`", `PressureGaugeEquivOn` is the
pressure gauge and `sobolevENorm` is `‖·‖_{H^s}`.  Time is the first spacetime
coordinate.  Nothing in this file re-defines a D01 object.

Five objects D01 does not define are defined here, because A02 is their first
consumer (`research/section4/STATEMENTS.md:1198-1199`, "`⟪D01:IsMaximalSolution⟫`
— one arity throughout: `ν a f u p` … DraftB has the lifespan but not yet the
predicate"; `:1209-1210`, "`⟪D01:limsupLeft⟫` … Not yet in DraftB"; `:1171`,
`⟪D01:normLinfty⟫`): `IsMaximalSolution`, `presingularTimes`, `limsupLeft`,
`speedENorm` and `timeShift`.

## The A01 interface

`research/A01/Spec.lean` is a draft under `research/`, not a Lean library
module, so it cannot be `import`ed by a file checked with
`cd verification && lake env lean ../research/A02/Spec.lean`.  The three
`LocalTheoryAPI` fields A02 consumes are therefore **restated verbatim** as the
first three fields of `MaximalSolutionAPI`, each tagged `⟪A01:…⟫`.  They are
copies, not weakenings: `horizon`, `solution` and `horizon_lower_bound` of
`research/A01/Spec.lean:283,297,338`.  `ManuscriptLocalRegularity` is *not*
restated — none of the statements below needs eq:projected, eq:Rpressure or the
all-order time smoothness, only the existence of a classical solution on a
positive horizon.  When A01 is registered under `verification/Contracts/`, these
three fields become one `LocalTheoryAPI` field.
-/

noncomputable section

namespace BlowupDensity.A02.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## 1. Objects A02 needs and `Data.lean` does not define -/

/-- `04-whole-space.tex:35` and `02-preliminaries.tex:47-48`: the left limit
superior `limsup_{t↑T} φ(t)`, valued in `ℝ≥0∞` so that unboundedness is
literally `= ⊤`.  This is `⟪D01:limsupLeft⟫` of
`research/section4/STATEMENTS.md:1209`, which records it as still owed by D01.

Used below only at `φ t = ‖u(t)‖_{L^∞}`, which is the manuscript's own
displayed quantity `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞` at `04-whole-space.tex:35`.
The equivalent "not bounded near `T`" restatement is deliberately not
substituted (`research/section4/STATEMENTS.md:350-351`). -/
def limsupLeft (T : ℝ) (φ : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup φ (nhdsWithin T (Iio T))

/-- `04-whole-space.tex:35`, `‖z(t)‖_{L^∞(R³)}`; `⟪D01:normLinfty⟫` of
`research/section4/STATEMENTS.md:1171`, which D01 does not yet define.

The essential supremum over `volume`, in the same slicewise spelling D01 uses
for the `L²` slices of `energyEssSup` (`Data.lean:444`,
`eLpNorm (fun x => z (t,x)) 2 volume`).  Every field it is applied to below is a
classical velocity, smooth on `Ico 0 T ×ˢ univ`
(`ClassicalSolutionR.velocity_smooth`), so the essential supremum is the
supremum and no measurability caveat bites; that identification is a lemma, not
part of this definition. -/
def speedENorm (z : SpatialField) : ℝ≥0∞ :=
  eLpNorm z ⊤ (volume : Measure Space)

/-- `appendix-a-local-theory.tex:147-150`, "restarting at `t₀ ↑ S`": the force
seen by the restarted problem, `f(· + t₀)`.  Time is the first spacetime
coordinate, so this is a translation of the time slot only.

The restart datum is the velocity slice `u(t₀,·)`, which needs no separate
notation. -/
def timeShift (t₀ : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z : SpaceTime => f (z.1 + t₀, z.2)

/-- `02-preliminaries.tex:32`: the times strictly before the maximal classical
lifespan, `[0, T^ν_{max,R}(a,f))` read inside `ℝ`.

`maximalLifespanR` is an `ℝ≥0∞`-valued supremum, so the comparison is made
after `ENNReal.ofReal`.  Strictness is the right condition and not a
convenience: `maximalLifespanR` is a supremum over *horizons carrying a
solution*, and a solution on `[0,S)` exists for every `S` below the supremum,
whereas at the supremum itself the manuscript asserts nothing. -/
def presingularTimes (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < maximalLifespanR ν a f}

/-- `02-preliminaries.tex:32,105` and `appendix-a-local-theory.tex:124-125`:
`(u,p)` **is** the maximal classical solution for the datum `(ν,a,f)`.

`⟪D01:IsMaximalSolution⟫` in the arity `ν a f u p` fixed by
`research/section4/STATEMENTS.md:1198` and consumed as
`RInsertAPI.isSol` (`:346`) and `RMainAPI.regularReferenceRider` (`:174`).

Two clauses:

* the lifespan is positive — without it the second clause is vacuously true of
  every pair when the datum carries no solution at all, since the empty
  supremum of `maximalLifespanR` is `0` (`Data.lean:650-657`);
* `u` and `p` are, *literally*, the velocity and pressure of a classical
  solution on `[0,S)` for **every** `S` below the maximal lifespan.  Together
  these say `(u,p)` is a solution on the whole of `[0,T^ν_{max,R})`.

Literal equality of the fields, rather than agreement on the slab, is what
makes the predicate usable: `ClassicalSolutionR` constrains its `velocity` and
`pressure` only on `Ico 0 S ×ˢ univ` (`Data.lean:624-648`), so a solution whose
slab restriction is `u` can always be presented with `velocity = u`, and
downstream statements about `u` outside `[0,S)` — Theorem 4.2's
`u_ε = v` window and its force support after `T` — stay meaningful.

*Maximality is not a third clause.*  That the interval cannot be enlarged is
the definition of `maximalLifespanR`, not a property of `(u,p)`; that `(u,p)`
is *the* maximal solution rather than *a* maximal solution is
`MaximalSolutionAPI.maximal_unique`, which rests on `UniquenessAPI`. -/
def IsMaximalSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanR ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanR ν a f →
      ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p

/-! ## 2. Uniqueness in the manuscript class -/

/-- **The uniqueness half of `prop:local` on `R³`**
(`paper/sections/02-preliminaries.tex:105`, "a unique maximal smooth velocity,
with pressure determined as above"), derived at
`paper/sections/appendix-a-local-theory.tex:115-125`.

Two classical solutions of the *same* whole-space datum `(ν,a,f)` on horizons
`T₁` and `T₂` have the same velocity on the common interval
`[0, min(T₁,T₂))`, and their pressures differ there by a function of time only.

**Hypotheses are exactly the manuscript's.**  `02-preliminaries.tex:105-107`
quantifies over "each initial velocity in the stated class and each force
smooth into every `H^m` on compact time intervals", i.e. `a ∈ X_R` and
`f ∈ F_R` (`Data.lean` `initialClassR`, `MemForceR`), at a viscosity `ν > 0`.
Nothing else is assumed: no smallness, no common horizon, no compact support,
no `p ∈ L²`.  The Grönwall coefficient `‖∇u₂‖_∞` is finite on compact common
intervals because `ClassicalSolutionR.sobolev` (`Data.lean:643`) already gives
`u₂ ∈ C([0,S];H^m)` for every `m`, which is the appendix's "since
`u₂ ∈ C_tH³`" (`appendix-a-local-theory.tex:122`); it is therefore a step of
the proof, not a field of this contract.

*Why the two clauses are separate.*  The velocity clause is the manuscript's
Grönwall.  The pressure clause is the manuscript's "the scalar pressure is
determined up to a function of time" (`02-preliminaries.tex:31`) *applied to
the difference of two solutions*: equal velocities force equal pressure
gradients through `ClassicalSolutionR.momentum` at interior times, and `R³` is
connected, so the difference is spatially constant on `Ioo 0 (min T₁ T₂)`;
continuity of `pressure` at `t = 0` (`pressure_smooth` on `Ico 0 T ×ˢ univ`)
carries it to the closed left endpoint, which is why the interval below is
`Ico` and not `Ioo`.

*No legacy-`Flow` equivalence is claimed.*  `Source/SmoothLifespan.lean:23`
`Flow` carries `energy`, `velocity_bound` and `derivative_bound` and omits
`sobolev` and `pressure_gradient`; only the source-to-manuscript direction
needed by the inserted field is in scope
(`formalization/blueprint/DEPENDENCY_GRAPH.md:188`). -/
structure UniquenessAPI where
  /-- `appendix-a-local-theory.tex:119-124`: equal data give equal velocities on
  the common interval.  `Ico 0 (min T₁ T₂)` is the intersection of the two
  half-open intervals of definition, including the initial time. -/
  velocity_unique : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
          u₁.velocity (t, x) = u₂.velocity (t, x)
  /-- `02-preliminaries.tex:31,105` "with pressure determined as above":
  the two pressures agree up to the gauge freedom `p ∼ p + κ(t)` on the same
  common interval.  `PressureGaugeEquivOn` (`Data.lean:589`) is exactly that
  relation. -/
  pressure_gauge : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        PressureGaugeEquivOn (Ico (0 : ℝ) (min T₁ T₂)) u₁.pressure u₂.pressure

/-! ## 3. The maximal solution and its lifespan -/

/-- **Patching, the maximal lifespan, the quantitative restart, and the
identification Theorem 4.2 uses.**

`paper/sections/02-preliminaries.tex:32` ("local uniqueness defines a maximal
classical lifespan"), `:105` (`prop:local`),
`paper/sections/appendix-a-local-theory.tex:124-125` (patching) and `:147-152`
(the restart), together with `paper/sections/04-whole-space.tex:53` (the
lifespan of the inserted solution is exactly `T`).

The first three fields are A01's, restated (see the header).  Everything after
`uniqueness` is A02's own obligation.

**What each consumer takes.**

* `R42` (`research/section4/STATEMENTS.md:310-313`, `:330-346`) takes
  `referenceLifespan` for its `reference`/`referenceLifespan` pair, and
  `insertion_lifespan_eq` for `lifespan` and `isSol`.
* `A04` (`DEPENDENCY_GRAPH.md:205-209`) takes `restart`, `restart_datum`,
  `restart_force` and `uniqueness`: the continuation criterion restarts at
  `t₀ ↑ S` with `H¹`-bounded data and identifies the extension with the
  original solution on the overlap.
* `C01` (`DEPENDENCY_GRAPH.md:275-279`) takes `IsMaximalSolution` and
  `exists_maximal`: the energy identities `eq:RL2` and `eq:RH1` are computed
  along *the* solution on `presingularTimes`.
* `breakdownSetIn` (`Data.lean:672`) is `{f ∈ Y : maximalLifespanR ν a f ≤
  ENNReal.ofReal T}`; `lifespan_le_iff` and `lifespan_le_iff_no_extension` are
  the two shapes in which membership is decided. -/
structure MaximalSolutionAPI where
  /-- ⟪A01:LocalTheoryAPI.horizon⟫ (`research/A01/Spec.lean:283`).  The common
  existence horizon `T₀(ν,a,f) > 0` of `02-preliminaries.tex:117`, total as a
  function so that no choice principle is needed to name it. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ
  /-- ⟪A01:LocalTheoryAPI.solution⟫ (`research/A01/Spec.lean:297`).  The local
  classical solution on `[0,T₀)` for every manuscript datum. -/
  localSolution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ClassicalSolutionR ν a f (horizon ν a f)
  /-- ⟪A01:LocalTheoryAPI.horizon_lower_bound⟫
  (`research/A01/Spec.lean:338`), the uniform step of
  `appendix-a-local-theory.tex:147-150`: on any `H¹` ball one `δ > 0` lies
  below every horizon.  `δ` is chosen **before** the datum; that quantifier
  order is the whole content, and it is what `restart` below cashes in. -/
  horizonLowerBound : ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField),
        a ∈ initialClassR → MemForceR f →
          sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K →
            δ ≤ horizon ν a f
  /-- The uniqueness half of `prop:local`, `§2` above.  Carried as a field
  rather than as a hypothesis of the individual statements because *every*
  clause below is a consequence of uniqueness together with A01. -/
  uniqueness : UniquenessAPI
  /-- `appendix-a-local-theory.tex:124` "Patching these local solutions":
  restriction to a shorter positive horizon, with the *same* velocity and
  pressure fields.

  The manuscript uses this silently at every "the solution on `[0,T']`,
  `T' < T`" (`04-whole-space.tex:53`, `research/section4/STATEMENTS.md:310`).
  It is the analogue of `Source/SmoothLifespan.lean:83` `Flow.restrict`, on the
  manuscript's class instead of `Flow`. -/
  restrict : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), ∀ S : ℝ, 0 < S → S ≤ T →
      ∃ w : ClassicalSolutionR ν a f S,
        w.velocity = u.velocity ∧ w.pressure = u.pressure
  /-- `appendix-a-local-theory.tex:124-125`: two local solutions of the same
  datum patch to one solution on the union of their intervals, agreeing with
  each on its own interval and with each pressure up to the gauge.

  This is the step that makes `maximalLifespanR` — a supremum over unrelated
  horizons (`Data.lean:657`) — the lifespan of a single solution; without it
  the supremum is only an order-theoretic bound.  It is also what
  `exists_maximal` below is built from. -/
  patch : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        ∃ w : ClassicalSolutionR ν a f (max T₁ T₂),
          (∀ t ∈ Ico (0 : ℝ) T₁, ∀ x : Space,
              w.velocity (t, x) = u₁.velocity (t, x)) ∧
          (∀ t ∈ Ico (0 : ℝ) T₂, ∀ x : Space,
              w.velocity (t, x) = u₂.velocity (t, x)) ∧
          PressureGaugeEquivOn (Ico (0 : ℝ) T₁) u₁.pressure w.pressure ∧
          PressureGaugeEquivOn (Ico (0 : ℝ) T₂) u₂.pressure w.pressure
  /-- `research/A01/Spec.lean:371-372`, the inequality A01 explicitly assigns to
  A02: the local horizon is below the maximal lifespan.  Immediate from
  `localSolution` and the definition of the supremum, and the reason
  `maximalLifespanR ν a f > 0` on every manuscript datum. -/
  horizon_le_lifespan : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanR ν a f
  /-- `02-preliminaries.tex:105` "has a unique maximal smooth velocity":
  **existence** of the maximal solution for every admissible datum, attaining
  `maximalLifespanR` in the sense of `IsMaximalSolution` — a classical solution
  on `[0,S)` for every `S` below the maximal lifespan, with one velocity and
  one pressure field serving all of them.

  Given A01 (`localSolution`) and `patch`, this is the manuscript's own
  construction; the definite article of `04-whole-space.tex:32` ("*the*
  solution for `a ∈ X_R` and `g ∈ F_R`") is exactly this field together with
  `maximal_unique`. -/
  exists_maximal : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∃ (u : SpaceTimeField) (p : SpaceTimeScalar), IsMaximalSolution ν a f u p
  /-- `02-preliminaries.tex:105`, the word "unique": any two maximal solutions
  of the same datum have the same velocity at every presingular time and
  gauge-equivalent pressures there.  The `R42` risk note
  `research/section4/STATEMENTS.md:393-395` ("the definite article presupposes
  uniqueness (A02)") is discharged by this field. -/
  maximal_unique : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
        IsMaximalSolution ν a f u₁ p₁ → IsMaximalSolution ν a f u₂ p₂ →
          (∀ t ∈ presingularTimes ν a f, ∀ x : Space, u₁ (t, x) = u₂ (t, x)) ∧
          PressureGaugeEquivOn (presingularTimes ν a f) p₁ p₂
  /-- `02-preliminaries.tex:42` eq:Rsingularforces through `Data.lean:672`
  `breakdownSetIn`: membership `T^ν_{max,R}(a,f) ≤ T` is exactly "no classical
  solution has a horizon beyond `T`".

  The order-theoretic content of `maximalLifespanR` being a supremum; the
  analogue of `Source/SmoothLifespan.lean:48` `lifespan_le_iff` on the
  manuscript's class.  `0 ≤ T` is needed because `ENNReal.ofReal` collapses the
  negative reals. -/
  lifespan_le_iff : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 ≤ T →
      (maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
        ∀ S : ℝ, Nonempty (ClassicalSolutionR ν a f S) → S ≤ T)
  /-- The same characterization in the contrapositive shape Theorem 4.2 argues
  in (`04-whole-space.tex:53`, "An extension through `T` would be … thus its
  maximal lifespan is exactly `T`"): the analogue of
  `Source/SmoothLifespan.lean:58` `lifespan_le_iff_no_extension`. -/
  lifespan_le_iff_no_extension : ∀ (ν : ℝ) (a : SpatialField)
      (f : SpaceTimeField) (T : ℝ), 0 ≤ T →
      (maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
        ∀ S : ℝ, T < S → IsEmpty (ClassicalSolutionR ν a f S))
  /-- The lower half of "`T^ν_{max,R}(a,g_ε) = T` exactly"
  (`04-whole-space.tex:34,53`): a solution on every strictly shorter interval
  pushes the lifespan up to `T`.  The analogue of
  `Source/SmoothLifespan.lean:101` `lifespan_ge_of_forall_shorter`.

  Together with `lifespan_le_of_unbounded` this is the equality Theorem 4.2
  states; `insertion_lifespan_eq` is the two of them packaged in the
  manuscript's configuration. -/
  lifespan_ge_of_forall_shorter : ∀ (ν : ℝ) (a : SpatialField)
      (f : SpaceTimeField) (T : ℝ), 0 < T →
      (∀ b : ℝ, 0 < b → b < T → Nonempty (ClassicalSolutionR ν a f b)) →
        ENNReal.ofReal T ≤ maximalLifespanR ν a f
  /-- `02-preliminaries.tex:34-36` against `:32`: "regular through `T`" and
  "`T` is strictly below the maximal lifespan" are the same condition.

  `RegularThrough ν a f T` (`Data.lean:664`) is `∃ δ > 0`, a classical solution
  on `[0,T+δ)`.  The forward direction is the definition of the supremum; the
  backward direction shrinks a horizon above `T` by half.  Used by R42 and by
  the second case of the proof of Theorem 4.1
  (`04-whole-space.tex:177`, `research/section4/STATEMENTS.md:199-203`, whose
  deferred `δ := (min(T_max, T+1) − T)/2` is this field). -/
  regularThrough_iff : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
      (T : ℝ), 0 < T →
      (RegularThrough ν a f T ↔ ENNReal.ofReal T < maximalLifespanR ν a f)
  /-- `04-whole-space.tex:32` "the solution … regular through `T+δ` for some
  `δ > 0`", in the shape R42 declares as `reference` together with
  `referenceLifespan : T + δ < ⟪D01:Tmax⟫ ν a g`
  (`research/section4/STATEMENTS.md:332-333`).

  A `RegularThrough` hypothesis gives a solution on `[0,T+δ)`, which bounds the
  lifespan below by `ofReal (T+δ)` but not *strictly*; halving the margin
  supplies the strict inequality R42's skeleton asks for, on a solution that
  still reaches past `T`.  This is the field that turns the manuscript's nested
  margin (risk note **O2**, `research/section4/STATEMENTS.md:388-392`) into one
  usable `δ`. -/
  referenceLifespan : ∀ (ν : ℝ) (a : SpatialField) (g : SpaceTimeField)
      (T : ℝ), 0 < T → RegularThrough ν a g T →
      ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionR ν a g (T + δ)) ∧
        ENNReal.ofReal (T + δ) < maximalLifespanR ν a g
  /-- `appendix-a-local-theory.tex:147-152`, the restart datum: the velocity
  slice at a presingular time is again an admissible initial velocity,
  `u(t₀,·) ∈ X_R = H^∞ ∩ L²_σ`.

  Immediate from `ClassicalSolutionR.sobolev` and `.divergence` at `t₀`
  (`Data.lean:643,638`), but it must be stated: without it the restarted
  problem is outside the class A01's `localSolution` accepts. -/
  restart_datum : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar), IsMaximalSolution ν a f u p →
        ∀ t₀ ∈ presingularTimes ν a f,
          (fun x : Space => u (t₀, x)) ∈ initialClassR
  /-- `appendix-a-local-theory.tex:150-151` "`f` is bounded into `H¹` on
  `[0,S+1]`": the shifted force is again in `F_R`.

  `MemForceR` (`Data.lean:544`) asks for smoothness on `R³ × [0,∞)` and finite
  `L¹_t`/`L²_t` norms of every order-`m` datum path over `(0,∞)`; shifting the
  time origin forward by `t₀ ≥ 0` restricts both integrals to a subinterval and
  preserves the one-sided smoothness at the new origin.  Nothing is claimed for
  `t₀ < 0`. -/
  restart_force : ∀ (f : SpaceTimeField), MemForceR f →
    ∀ t₀ : ℝ, 0 ≤ t₀ → MemForceR (timeShift t₀ f)
  /-- **The quantitative restart** (`appendix-a-local-theory.tex:147-152`):
  "The `H¹` local existence bounds … give a common positive existence duration
  when restarting at `t₀ ↑ S`: the initial `H¹` norms stay bounded, and `f` is
  bounded into `H¹` on `[0,S+1]` … One interval extends beyond `S`, and
  uniqueness identifies it with the original solution on the overlap."

  For each viscosity and each finite `H¹` bound `K` there is one step `δ > 0`
  such that *every* presingular restart time whose datum and shifted force obey
  `K` pushes the lifespan to at least `t₀ + δ`.  The quantifier order — `δ`
  before `(a,f,u,p,t₀)` — is A01's `horizonLowerBound` quantifier order, and is
  the whole point: a restart family with bounded `H¹` data gets **one** step
  length, which is what lets `t₀ ↑ S` overshoot `S`.

  *Where uniqueness enters.*  The restarted local solution of A01 is a solution
  of the *shifted* problem; that its concatenation with the original is again a
  classical solution of `(ν,a,f)` — the manuscript's "uniqueness identifies it
  with the original solution on the overlap" — is `uniqueness` plus `patch`.
  The conclusion is stated as a lifespan bound rather than as a produced
  solution because `maximal_unique` already names the resulting field: the
  extension *is* `u`, on the longer interval.

  A04's continuation criterion consumes exactly this field
  (`DEPENDENCY_GRAPH.md:205-209`); A02 does not state `eq:criterion`. -/
  restart : ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField) (u : SpaceTimeField)
        (p : SpaceTimeScalar),
        a ∈ initialClassR → MemForceR f → IsMaximalSolution ν a f u p →
          ∀ t₀ ∈ presingularTimes ν a f,
            sobolevENorm 1 (fun x : Space => u (t₀, x)) ≤ K →
            forceSobolevENormL1 1 (timeShift t₀ f) ≤ K →
              ENNReal.ofReal (t₀ + δ) ≤ maximalLifespanR ν a f
  /-- The upper half of Theorem 4.2's "`T^ν_{max,R}(a,g_ε) = T` exactly"
  (`04-whole-space.tex:53`): "An extension through `T` would be bounded in
  `C_tH²` on a neighbourhood of `T` … contradicting the blowup".

  If `(u,p)` is a classical solution on every `[0,S)` with `S < T` and its
  speed has `limsup_{t↑T} = ⊤`, then no classical solution of the same datum
  reaches beyond `T`, so the lifespan is at most `T`.  The argument is
  `uniqueness` — an extension would have velocity `u` on `[0,T)` — followed by
  the manuscript's own two steps: the extension's `H²` datum path is
  *continuous* on `Ico 0 S ⊇ Icc 0 T` (`ClassicalSolutionR.sobolev` at `m = 2`,
  `Data.lean:643`), hence bounded there, and `‖z‖_∞ ≤ C‖z‖_{H²}` of
  `eq:Rproduct` turns that into an `L^∞` bound.

  The second step is **A03**, and the DAG does not yet carry `A03 → A02`; the
  header and `research/A02/COMPARISON.md` §5 record why that edge is needed by
  the uniqueness field as well, and therefore why the hypothesis is written in
  the manuscript's `L^∞` norm rather than converted upstream. -/
  lifespan_le_of_unbounded : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
      (T : ℝ), 0 < ν → a ∈ initialClassR → MemForceR f → 0 < T →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        (∀ S : ℝ, 0 < S → S < T →
            ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p) →
        limsupLeft T (fun t => speedENorm (fun x : Space => u (t, x))) = ⊤ →
          maximalLifespanR ν a f ≤ ENNReal.ofReal T
  /-- **The identification Theorem 4.2 needs**, in the manuscript's own
  configuration (`04-whole-space.tex:31-37,53`).

  Data: a reference solution `(v,π)` for `(a,g)` regular through `T`, a
  perturbed force `g_ε ∈ F_R`, and a field `(u,p)` that is a classical solution
  for `(a,g_ε)` on every `[0,S)` with `S < T`, coincides with the reference on
  `[0, T − 2ε²]` and whose speed blows up at `T`.  Conclusion, exactly the
  two clauses R42 declares (`research/section4/STATEMENTS.md:345-347`):
  `T^ν_{max,R}(a,g_ε) = T`, and `(u,p)` **is** the maximal solution for that
  datum — "Proposition 2.1 identifies the solution with the unique maximal
  solution" (`04-whole-space.tex:53`).

  *Which hypotheses do the work.*  The `≥` half is
  `lifespan_ge_of_forall_shorter` applied to the presingular family; the `≤`
  half is `lifespan_le_of_unbounded`; `IsMaximalSolution` then follows because
  the maximal lifespan has been pinned to `ofReal T` and the family already
  covers every `S < T`.  The reference clauses `RegularThrough` and
  `referencePresingular`, and the window `u = v` on `[0, T − 2ε²]`, are the
  manuscript's configuration — they are what R42 has in hand and what makes the
  statement recognisable as `04-whole-space.tex:36` — and are not needed by
  either half; a consumer that only wants the equality should use the two
  fields above.

  `2ε² < T` is Theorem 4.2's own smallness constraint on `ε`
  (`research/section4/STATEMENTS.md:418-423`, "`2ε² < min(T,δ)`"), kept so that
  the agreement window is a nonempty subinterval of `[0,T)`. -/
  insertion_lifespan_eq : ∀ (ν : ℝ) (a : SpatialField) (g gPert : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR g → MemForceR gPert →
      ∀ T ε : ℝ, 0 < T → 0 < ε → 2 * ε ^ 2 < T →
        ∀ (v : SpaceTimeField) (π : SpaceTimeScalar),
          RegularThrough ν a g T →
          (∀ S : ℝ, 0 < S → S < T →
              ∃ w : ClassicalSolutionR ν a g S,
                w.velocity = v ∧ w.pressure = π) →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            (∀ S : ℝ, 0 < S → S < T →
                ∃ w : ClassicalSolutionR ν a gPert S,
                  w.velocity = u ∧ w.pressure = p) →
            (∀ t : ℝ, 0 ≤ t → t ≤ T - 2 * ε ^ 2 → ∀ x : Space,
                u (t, x) = v (t, x)) →
            limsupLeft T
                (fun t => speedENorm (fun x : Space => u (t, x))) = ⊤ →
              maximalLifespanR ν a gPert = ENNReal.ofReal T ∧
                IsMaximalSolution ν a gPert u p

end BlowupDensity.A02.Draft
