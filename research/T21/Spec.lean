import Contracts.V1.Data
import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Bindings.TorusLocalTheory
import NSFormalization.Section3.T20.CriticalRegularity

/-!
# T21: the main assembly on `T³`
# (`cor:nondensity` `03-torus.tex:506-520` and `thm:main` `:6-16`)

Reconciled, statement-only specification of the T21 node
(`collaboration/SECTION3_PLAN.md` §3, row T21), assembled from the two
double-blind drafts (lane 410 = draft A, lane 411 = draft B) under
`research/T21/RECONCILIATION.md`.  **This file contains no proofs of any API
field**; the only terms are five deliberate drift/seam checks (§0.2 and §5).

It renders, clause by clause, the two top-level results of Section 3:

* `NonDensityAPI`  — `cor:nondensity`, non-density at and above the critical
  order (`:506-509`, proof `:510-520`);
* `MainTheoremAPI` — `thm:main`, the Sobolev density threshold, clauses (i)
  and (ii) (`:6-16`, proof `:522-524`).

The scope remark `:525` ("the behavior for general nonzero initial velocities
at or above the critical order remains outside this classification") states
what is *not* proved and is deliberately not a field.

## Reconciled bases (per structure)

Per `RECONCILIATION.md` §2: `NonDensityAPI` → base **B** (indexed by the real
`c`, nine fields), `MainTheoremAPI` → base **B** with draft A's binder order on
`fixedInitialDensity`.  Both structures are **`Prop`-valued**: neither result
introduces a constant or a datum.  `cor:nondensity`'s only constant is
`prop:critical`'s, which enters as the structure index `c` and is pinned to a
genuine `prop:critical` constant by the fields `hc` and
`criticalGlobalRegularity`; `thm:main`'s only number is the literal threshold
`1/2`, pinned to the registered `criticalOrder 1`.  This follows the T19/T24
data-free `Prop` precedent and diverges from the `Type`-valued registry
convention of `Contracts/V1/MainThresholds.lean` (owner question,
`RECONCILIATION.md` §3).

## Vocabulary and copy policy (`CLAUDE.md`, T13 copy policy)

Everything **registered** is imported and used by name, never restated:
`ClassicalSolutionT`, `maximalLifespanT`, `RegularThroughT`, `breakdownSetT`,
`breakdownSetInT`, `RelativelyDenseT`, `forceClassT`, `initialClassT`,
`forceSobolevENormT`, `periodicSobolevENorm`, `criticalOrder`
(`Contracts/V1/TorusLocalTheory.lean`, `Contracts/V1/TorusData.lean`,
`Contracts/V1/Data.lean`).  Every lifespan in this file is the **registered**
`maximalLifespanT`.

Two upstream inputs are unregistered, and they are treated differently
(`RECONCILIATION.md` §2):

* **T19 `prop:density`** has no canonical module (only
  `NSFormalization/Section3/T19/Bookkeeping.lean`, which contains the U1–U6
  lemmas, not the record), so `BlowupDensity.T19.PeriodicDensityAPI` and
  `periodicDensityStatement` are **copied verbatim** from
  `research/T19/Spec.lean:184-255`.  The other three T19 structures
  (`MixedRegionAPI`, `StrongClosureAPI`, `ProjectionAPI`) are the
  `03-torus.tex:527-590` corollaries of `prop:density` and are **not** consumed
  by `thm:main`, so — unlike both drafts — they are not copied here.
* **T20 `prop:critical`** *does* have a canonical module, so it is
  **imported**, not copied: `NSFormalization.Section3.T20.CriticalRegularityTAPI`
  is named directly in the assembly signatures of §4.  Only its `c : ℝ` field is
  used there; §5 checks in Lean that its `globalRegularity`, which speaks the
  *canonical* `NSFormalization.Section3.T10.maximalLifespanT`, discharges the
  registered-vocabulary field `criticalGlobalRegularity` through
  `BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq`.  The canonical
  and registered `ClassicalSolutionT` are distinct inductives
  (`CLAUDE.md` structure exception), so that bridge is a `rw`, not an `rfl`.

## What differs from the Section 4 counterpart

`Contracts/V1/MainThresholds.lean` (`R41`, `04-whole-space.tex:7-15`) is the
same two-clause theorem with three differences (`RECONCILIATION.md` §1):

1. a **single** critical exponent and **`q = 1` only** — the torus has a
   spectral gap, so `q ∈ {1,2}` and `s_q = 2/q - 3/2` collapse to
   `criticalOrder 1 = 1/2` (`collaboration/SECTION3_PLAN.md` §4);
2. `thm:main` carries **no regular-reference rider**: R41's
   `regularReferenceApproximation` (`04-whole-space.tex:13`) lives on the torus
   in `cor:closure` = `BlowupDensity.T19.StrongClosureAPI`, not here;
3. the non-density half goes through an **explicit ball of radius `cν`**
   (`:511-519`); R41 states only the biconditional and keeps the ball inside
   its own converse (`R41.criticalRadius_le_forceSobolevENorm`).
-/

noncomputable section

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal Topology BigOperators

/-! ## 0.1 The consumed T19 input, copied verbatim

Copied verbatim from `research/T19/Spec.lean:184-255` (the reconciled
`prop:density` record and its paper-order alias), keeping its source namespace.
Its dependencies resolve through the registered `Contracts.V1.TorusLocalTheory`
/ `Contracts.V1.Data` imports above, exactly as in the source file. -/

namespace BlowupDensity.T19


/-- **`prop:density` — density for each fixed initial velocity,
`paper/sections/03-torus.tex:349-356`, proof `:357-368`.**

For `a ∈ 𝓧`, `ν>0`, `T>0`, `s<1/2`: every force `g ∈ 𝓕` is approximated in the
relative `L^1_tH^s_x` topology by a force whose maximal lifespan is at most `T`.
`Prop`-valued: no datum or constant is exported (the constants are internal to
`thm:insertion`).  Base B (`RECONCILIATION.md` §3). -/
structure PeriodicDensityAPI : Prop where
  /-- `03-torus.tex:350-355`, the whole proposition: for `a ∈ 𝓧`, `ν>0`, `T>0`
  and `s<1/2`, the breakdown set `B_{ν,a,T}` is relatively dense in `𝓕` for the
  `L^1_tH^s_x` pseudometric.  Registered `RelativelyDenseT 1 s forceClassT
  (breakdownSetT ν a T)` unfolds to exactly the paper's display `:352-354`
  `∀ g∈𝓕 ∀ρ>0 ∃f: ‖f-g‖_{L^1_tH^s} < ρ ∧ T_max^ν(a,f) ≤ T`
  (`f ∈ breakdownSetT` is `f∈𝓕 ∧ maximalLifespanT ν a f ≤ ofReal T`).

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ s, s<1/2 →`
  density.  `1/2 = criticalOrder 1` (the torus fixes `q=1`, `SECTION3_PLAN.md`
  §4), written literally as `03-torus.tex:350`.

  Non-vacuity: the conclusion is the registered positive-radius density
  predicate, whose distance is the fail-safe `ℝ≥0∞` norm `forceSobolevENormT`,
  and whose witness must live in the registered breakdown set — never `True`. -/
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

  /-- `03-torus.tex:350` and `04-whole-space.tex:8`: the sub-critical threshold
  `1/2` of `prop:density` is the registered `criticalOrder 1` (`= 2/1 - 3/2`).

  Exact quantifier order: none.  This pins the torus threshold to the same
  arithmetic as `MainThresholdsAPI.thresholdValues`.

  Non-vacuity: a concrete real equality, not an opaque proposition; the value
  `criticalOrder 1` is the registered threshold function evaluated at `q=1`. -/
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2

  /-- `03-torus.tex:363-365` (regular-reference case of the proof) and the
  distinction of `:590`: around every reference force that is regular through
  `T` (`RegularThroughT`, i.e. `T_max^ν(a,g) > T`), `thm:insertion` yields, at
  every sub-critical `s` and every positive radius `r`, a nearby torus force
  whose maximal lifespan is *exactly* `T` — sharper than the `≤ T` of
  `fixedInitialDensity`, which uses "breakdown by `T`" so that an
  already-earlier-breaking reference may be left unchanged.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ g, g∈𝓕 →`
  `RegularThroughT ν a g T → ∀ s, s<1/2 → ∀ r, 0<r →`
  `∃ f∈𝓕, forceSobolevENormT 1 s (f-g) < r ∧ maximalLifespanT ν a f = ofReal T`.

  Non-vacuity: the lifespan conclusion is an *exact* `ℝ≥0∞` equality with
  `ofReal T` (the "singularity exactly at `T`" of `thm:insertion`), not the
  one-sided `≤` of the density set; `RegularThroughT` is the registered
  "regular through `T`" hypothesis and the distance is the registered
  `forceSobolevENormT`, strictly below `r`. -/
  regularReferenceSingular :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT → RegularThroughT ν a g T →
          ∀ s : ℝ, s < 1 / 2 → ∀ r : ℝ≥0∞, 0 < r →
            ∃ f ∈ forceClassT,
              forceSobolevENormT 1 s (fun z => f z - g z) < r ∧
                maximalLifespanT ν a f = ENNReal.ofReal T

/-- **`prop:density` in the paper's quantifier order, `03-torus.tex:350-355`.**
The headline proposition; equals field `PeriodicDensityAPI.fixedInitialDensity`. -/
def periodicDensityStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

end BlowupDensity.T19

/-! # T21: the node's own declarations

Nothing below is copied.  Every norm is `ℝ≥0∞`-valued (`forceSobolevENormT`,
`periodicSobolevENorm`), so a missing representative reports `⊤` rather than a
junk zero; every viscosity and horizon carries `0 < ν`, `0 < T`; there is no
real supremum and no `.toReal`. -/

namespace BlowupDensity.T21

/-! ## 0.2 The two sets named in the statements -/

-- from DraftB:1034 (`breakdownSetTZero`); DraftA:1202 spells the same datum as
-- a separate `def zeroInitialVelocity` and never names `𝓑⁰`.
/-- `02-preliminaries.tex:38-41` `eq:singularforces`, second display, and
`03-torus.tex:10,12`: `𝓑⁰_{ν,T} = 𝓑_{ν,0,T}`, the forces producing classical
breakdown by `T` from the zero initial velocity.  The torus mirror of the
registered whole-space `Data.breakdownSetRZero`, whose own docstring records
that `𝓑⁰_{ν,T}` is the *torus* symbol.  The zero datum is spelled
`fun _ : Space ↦ 0`, the literal used by
`NSFormalization.Section3.T20.CriticalRegularityTAPI.globalRegularity`, so the
two compose without a rewrite. -/
def breakdownSetTZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetT ν (fun _ : Space ↦ 0) T

-- from DraftB:1044 (`criticalBallT`, parameterized by the order `s`);
-- DraftA:1214 `criticalForceBall` fixes `s = 1/2` and is parameterized by the
-- whole T20 record, so it cannot express the ball of `:519`.
/-- `03-torus.tex:511-514` and `:519`: the ball of the corollary's proof,
`{g ∈ 𝓕 : ‖g‖_{L¹_tH^s_x} < cν}`.  At `s = 1/2` this is the display `:513`,
whose radius is the `prop:critical` constant times the viscosity; at a general
`s ≥ 1/2` it is the ball of `:519`.  The radius is `ENNReal.ofReal (c * ν)`,
matching `prop:critical`'s own smallness hypothesis `:387`, and the membership
`g ∈ forceClassT` keeps the ball *relative* to `𝓕` as `:515` requires. -/
def criticalBallT (c ν s : ℝ) : Set SpaceTimeField :=
  {g | g ∈ forceClassT ∧ forceSobolevENormT 1 s g < ENNReal.ofReal (c * ν)}

/-! ### Definitional drift checks against the registered and canonical
spellings (the only `rfl` terms in this file besides §5). -/

/-- The zero-datum torus breakdown set has the shape of the registered
whole-space `Data.breakdownSetRZero` (`Contracts/V1/Data.lean`). -/
example (ν T : ℝ) :
    BlowupDensity.Contracts.V1.Data.breakdownSetRZero ν T =
      BlowupDensity.Contracts.V1.Data.breakdownSetR ν (fun _ : Space ↦ 0) T :=
  rfl

/-- At `s = 1/2` the ball's norm is the canonical T20 `criticalRho`, i.e. the
registered `L¹(0,∞;H^{1/2}(T³))` norm of `Contracts/V1/TorusLocalTheory.lean`.
This is the seam between `:513` and `:387`. -/
example (g : SpaceTimeField) :
    NSFormalization.Section3.T20.criticalRho g = forceSobolevENormT 1 (1 / 2) g :=
  rfl

/-- `03-torus.tex:7` and `:508`, the relative topology unfolded: density in `𝓕`
for the `L¹(0,∞;H^s(T³))` pseudometric is approximation of every reference
force at every positive `ℝ≥0∞` radius.  This is why the last sentence of `:519`
("a dense subset cannot miss a nonempty open set") is not a field: it *is* this
definition, instantiated at `g = 0` and `r = ENNReal.ofReal (c * ν)`. -/
example (ν T s : ℝ) :
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) =
      (∀ g ∈ forceClassT, ∀ r : ℝ≥0∞, 0 < r →
        ∃ f ∈ breakdownSetTZero ν T, forceSobolevENormT 1 s (f - g) < r) :=
  rfl

/-! ## 1. `cor:nondensity` (`03-torus.tex:506-509`, proof `:510-520`)

**`Prop`-valued, indexed by the real `c`** (`RECONCILIATION.md` §2, base B).
`cor:nondensity` (`:507-508`) introduces no constant of its own; the only
constant in its proof is `prop:critical`'s (`:384`).  Making `c` an index rather
than threading the 21-field T20 record keeps the corollary statable in
registered vocabulary alone, and makes
`nonDensityOfCritical : ∀ K : CriticalRegularityTAPI, NonDensityAPI K.c` the
literal rendering of `:516` "by Proposition~\ref{prop:critical}".  The index is
prevented from being an arbitrary real by `hc` and `criticalGlobalRegularity`. -/

/-- **`cor:nondensity` — non-density at and above the critical exponent,
`paper/sections/03-torus.tex:506-509`, proof `:510-520`.**

For every `s ≥ 1/2` and `T > 0`, `𝓑⁰_{ν,T}` is not dense in `𝓕` for the relative
`L¹_tH^s_x` topology.  The proof exhibits the ball
`{g ∈ 𝓕 : ‖g‖_{L¹_tH^s_x} < cν}`: nonempty, relatively open, containing zero,
and — by `prop:critical` together with the Fourier-weight monotonicity of the
`H^s` norms — disjoint from the singular-force set.

`c` is the `prop:critical` constant (`:384`); `NonDensityAPI K.c` for
`K : NSFormalization.Section3.T20.CriticalRegularityTAPI` is the intended
instantiation (§4). -/
structure NonDensityAPI (c : ℝ) : Prop where
  -- from DraftB:1118 (`hc`).  DraftA:1246 `criticalRadius_pos`
  -- (`∀ ν, 0 < ν → 0 < ENNReal.ofReal (c*ν)`) is equivalent but derived; the
  -- paper's words at `:384` are "There is `c>0`".
  /-- `03-torus.tex:384`: positivity of the `prop:critical` smallness constant.

  Exact quantifier order: none; `c` is the structure index.

  Non-vacuity: with `0 < ν` this makes `ENNReal.ofReal (c * ν)` a strictly
  positive radius, so `criticalBallT c ν s` is a genuine ball rather than the
  empty set that would make every disjointness clause below vacuous. -/
  hc : 0 < c

  -- from DraftB:1131 (`criticalGlobalRegularity`), with the **registered**
  -- `maximalLifespanT`.  DraftA has no such field: it parameterizes the whole
  -- structure by `critical : CriticalRegularityTAPI` (DraftA:1238) and reads
  -- `critical.globalRegularity` instead.  §5 checks that the canonical T20
  -- record discharges this field.
  /-- `03-torus.tex:383-389` `prop:critical`, the imported input named at `:516`:
  a force in `𝓕` with `ρ = ‖g‖_{L¹(0,∞;H^{1/2})} < cν` has infinite maximal
  lifespan from rest.  This is
  `NSFormalization.Section3.T20.CriticalRegularityTAPI.globalRegularity`
  verbatim, except that `maximalLifespanT` is the registered one throughout
  this file (`CLAUDE.md` structure exception; the bridge is §5).

  Exact quantifier order: `∀ ν, 0 < ν → ∀ g, g ∈ 𝓕 →`
  `‖g‖_{L¹_tH^{1/2}} < ofReal (c*ν) → maximalLifespanT ν 0 g = ⊤`.

  Non-vacuity: it pins the index `c` to a constant for which `prop:critical`
  actually holds; the conclusion is the registered `ℝ≥0∞` lifespan being `⊤`,
  which is what makes the ball disjoint from every `𝓑⁰_{ν,T}`. -/
  criticalGlobalRegularity : ∀ ν : ℝ, 0 < ν →
    ∀ g : SpaceTimeField, g ∈ forceClassT →
      forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤

  -- from DraftB:1147 (`zeroMemBall`); merges DraftA:1256
  -- (`zeroForce_mem_forceClass`) and DraftA:1265 (`zero_mem_criticalBall`),
  -- whose first is literally the first conjunct of the second.
  /-- `03-torus.tex:515`, "is a nonempty relative open ball, containing zero":
  the zero force lies in the ball, at every order `s`.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ s : ℝ,`
  `(0 : SpaceTimeField) ∈ criticalBallT c ν s`.

  Non-vacuity: two genuine assertions at once — `0 ∈ 𝓕` (the zero force really
  is an admissible smooth, periodic, compactly-time-supported force) and
  `forceSobolevENormT 1 s 0 < ofReal (c*ν)`, i.e. the registered `⨅`-norm of the
  zero field is *attained*, not `⊤`.  It also supplies the nonemptiness that the
  last sentence of `:519` needs. -/
  zeroMemBall : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    (0 : SpaceTimeField) ∈ criticalBallT c ν s

  -- from DraftB:1162 (`ballRelativelyOpen`); absent from DraftA, which never
  -- renders the word "open" of `:515`.
  /-- `03-torus.tex:515`, "relative **open** ball": openness of the ball in the
  relative `L¹_tH^s_x` pseudometric on `𝓕`, stated in the same `ε`-form that
  `RelativelyDenseT` uses (there is no `TopologicalSpace` instance on the force
  class in the contract layer; `Paper1/ManuscriptTopology.lean` proves that the
  genuine relative topology's density is exactly this `ε`-form).

  Exact quantifier order: `∀ ν, 0 < ν → ∀ s, ∀ g ∈ criticalBallT c ν s,`
  `∃ r : ℝ≥0∞, 0 < r ∧ ∀ f ∈ 𝓕, ‖f - g‖_{L¹_tH^s} < r → f ∈ criticalBallT c ν s`.

  Non-vacuity: the radius `r` is quantified inside the ball point, so this is the
  honest "every point is interior"; discharging it needs the triangle inequality
  for the registered `⨅`-norm and is not implied by the definition of
  `criticalBallT`. -/
  ballRelativelyOpen : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    ∀ g ∈ criticalBallT c ν s,
      ∃ r : ℝ≥0∞, 0 < r ∧
        ∀ f ∈ forceClassT, forceSobolevENormT 1 s (f - g) < r →
          f ∈ criticalBallT c ν s

  -- from DraftB:1194 (`sliceSobolevMonotone`); absent from DraftA, which keeps
  -- only the time-integrated form.  DraftB:1180 `reweightContraction` (the
  -- coefficient mechanism behind this field) is dropped: it is the `:517`
  -- justification, one layer below the statement, and lives in the T10 data
  -- layer (`Contracts.V1.TorusData.IsPeriodicReweight`).  It is
  -- `RECONCILIATION.md` §4 proof unit N1.
  /-- `03-torus.tex:517-518`: `‖g(t)‖_{H^{1/2}} ≤ ‖g(t)‖_{H^s}` for `s ≥ 1/2`, on
  a single time slice — the inequality the paper actually displays.  The stated
  reason, "the Fourier weights imply", is the reweighting
  `Contracts.V1.TorusData.IsPeriodicReweight` by
  `periodicFrequencyWeight k ^ ((1/2 - s)/2) ≤ 1`; it is the proof of this field,
  not a separate clause.

  Exact quantifier order: `∀ s : ℝ, 1/2 ≤ s → ∀ z : SpatialField,`
  `periodicSobolevENorm (1/2) z ≤ periodicSobolevENorm s z`.

  Non-vacuity: no class hypothesis on `z` is needed and none is silently helping
  — both sides are the registered `⨅` over representing data, which is `⊤` when
  no datum exists, so this is a real comparison of two extended norms rather
  than of junk zeros. -/
  sliceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ z : SpatialField,
    periodicSobolevENorm (1 / 2) z ≤ periodicSobolevENorm s z

  -- from DraftB:1207 (`forceSobolevMonotone`, unconditional).  DraftA:1291
  -- `sobolevMonotonicity` is the same inequality with an extra
  -- `g ∈ forceClassT` hypothesis, which its proof never uses; the unconditional
  -- form is taken (`RECONCILIATION.md` §2).
  /-- `03-torus.tex:517-519`: the time-integrated form actually used,
  `‖g‖_{L¹_tH^{1/2}_x} ≤ ‖g‖_{L¹_tH^s_x}` for `s ≥ 1/2`.  It is what makes the
  `L¹_tH^s_x` ball of radius `cν` a subset of the `L¹_tH^{1/2}_x` ball, hence
  what turns `criticalBallDisjoint` into `ballDisjoint`.

  Exact quantifier order: `∀ s : ℝ, 1/2 ≤ s → ∀ f : SpaceTimeField,`
  `forceSobolevENormT 1 (1/2) f ≤ forceSobolevENormT 1 s f`.

  Non-vacuity: strictly stronger than the slice clause — the two sides are
  infima over *strongly measurable representing paths*, so discharging it
  requires transporting a whole path, not one datum. -/
  forceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ f : SpaceTimeField,
    forceSobolevENormT 1 (1 / 2) f ≤ forceSobolevENormT 1 s f

  -- from DraftB:1219 (`criticalBallDisjoint`, `Disjoint` spelling — the paper
  -- says "disjoint").  DraftA:1278 states the same fact in the unfolded
  -- element form `∀ g ∈ ball, g ∉ breakdownSet`, which `Set.disjoint_left`
  -- converts.
  /-- `03-torus.tex:511-516`: at `s = 1/2` the ball is disjoint from `𝓑⁰_{ν,T}`,
  by `prop:critical`.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T →`
  `Disjoint (criticalBallT c ν (1/2)) (breakdownSetTZero ν T)`.

  Non-vacuity: `Disjoint` between honest inhabited sets — `zeroMemBall` shows the
  first is nonempty — and the second is the registered breakdown set, so this is
  the actual separation the corollary needs, not disjointness from `∅`. -/
  criticalBallDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    Disjoint (criticalBallT c ν (1 / 2)) (breakdownSetTZero ν T)

  -- from DraftB:1232 (`ballDisjoint`); DraftA folds this step into `nonDensity`
  -- and therefore never states the `s ≥ 1/2` ball that its own
  -- `sobolevMonotonicity` field exists to serve.
  /-- `03-torus.tex:519`, first sentence: for every `s ≥ 1/2` the ball
  `‖g‖_{L¹_tH^s_x} < cν` is also disjoint from the singular-force set — the
  previous field combined with `forceSobolevMonotone`.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ s, 1/2 ≤ s →`
  `Disjoint (criticalBallT c ν s) (breakdownSetTZero ν T)`.

  Non-vacuity: `s` ranges over the whole critical-and-above half line and the
  ball keeps the same radius `cν` as at `s = 1/2`; nothing degenerates as `s`
  grows, because the ball only shrinks. -/
  ballDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
    Disjoint (criticalBallT c ν s) (breakdownSetTZero ν T)

  -- from DraftB:1247 (binder order `ν, s, T`, following `:507` "for every
  -- `s ≥ 1/2` and `T > 0`"); DraftA:1304 is the same `Prop` with `T` before `s`.
  /-- `03-torus.tex:507-508`, the corollary itself, with the last sentence of
  `:519` ("a dense subset cannot miss a nonempty open set") as its proof: for
  every `s ≥ 1/2` and `T > 0`, `𝓑⁰_{ν,T}` is **not** dense in `𝓕` for the
  relative `L¹_tH^s_x` topology.

  Exact quantifier order, following `:507`: `∀ ν, 0 < ν → ∀ s, 1/2 ≤ s →`
  `∀ T, 0 < T → ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)`.

  Non-vacuity: the negated predicate is the registered positive-radius density
  notion whose distance is the fail-safe `ℝ≥0∞` norm; refuting it means
  producing one reference force and one radius that no breakdown force meets,
  which is precisely the ball above. -/
  nonDensity : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

-- from DraftB:1252; DraftA:1374 is the same `Prop` with `T` before `s`.
/-- **`cor:nondensity` in the paper's quantifier order, `03-torus.tex:507-508`.**
Literally the field `NonDensityAPI.nonDensity`, and independent of `c`. -/
def nonDensityStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

/-- The zero-datum spelling inside `nonDensityStatement` is the registered
`breakdownSetT` at `a = 0`. -/
example :
    nonDensityStatement =
      (∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
        ¬ RelativelyDenseT 1 s forceClassT
            (breakdownSetT ν (fun _ : Space ↦ 0) T)) :=
  rfl

/-! ## 2. `thm:main` (`03-torus.tex:6-16`, proof `:522-524`, scope remark `:525`)

**`Prop`-valued** (`RECONCILIATION.md` §2): the theorem exports neither a
constant nor a datum; its only number is the literal threshold `1/2`, pinned
below to the registered `criticalOrder 1`. -/

/-- **`thm:main` — Sobolev density threshold,
`paper/sections/03-torus.tex:6-16`, proof `:522-524`.**

Equip `𝓕` with its relative `L¹(0,∞;H^s(T³))` norm topology (`:7`; on the torus
the time exponent is `q = 1` only, `collaboration/SECTION3_PLAN.md` §4).  Then
(i) for every fixed `a ∈ 𝓧` the set `𝓑_{ν,a,T}` is dense if `s < 1/2` (`:9`),
and (ii) for zero initial velocity `𝓑⁰_{ν,T}` is dense **iff** `s < 1/2`
(`:10-14`).

The proof `:523` names its two and only two inputs: `prop:density` (= T19
`PeriodicDensityAPI.fixedInitialDensity`) for the density half and
`cor:nondensity` (= `NonDensityAPI.nonDensity`) for the non-density half. -/
structure MainTheoremAPI : Prop where
  -- from DraftB:1298 (`thresholdValue`); absent from DraftA, which leaves the
  -- bridge to the copied T19 record.  Kept so that `MainTheoremAPI` is readable
  -- standalone and mirrors R41's `MainThresholdsAPI.thresholdValues`.
  /-- `03-torus.tex:9,13`: the torus threshold `1/2` is the registered Section 4
  threshold function at `q = 1`, `criticalOrder 1 = 2/1 - 3/2`.  The paper writes
  `1/2` literally, so every density field below writes it literally too; this
  field ties the two spellings together and reproduces the first conjunct of
  `Contracts/V1/MainThresholds.lean`'s `thresholdValues`.

  Exact quantifier order: none.

  Non-vacuity: a concrete equality of reals between the registered threshold
  function and the literal used in the statements, not an opaque proposition.
  On the torus this is the *only* threshold: `q = 2` has no torus counterpart
  (`SECTION3_PLAN.md` §4), so there is no second conjunct. -/
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2

  -- from DraftB:1309 (`zeroInitialClass`); absent from DraftA.  Without it,
  -- clause (ii)'s `⟸` direction cannot be obtained by specializing clause (i).
  /-- `03-torus.tex:10`, "For zero initial velocity", together with
  `02-preliminaries.tex:9` `eq:inputspaces`: the zero field is an admissible
  initial velocity, `0 ∈ 𝓧 = C^∞_div(T³;R³)`.

  Exact quantifier order: none.

  Non-vacuity: this is what makes clause (ii) an instance of clause (i) rather
  than a statement about a datum outside the class; it unfolds to smoothness,
  unit periodicity and solenoidality of `fun _ : Space ↦ 0`. -/
  zeroInitialClass : (fun _ : Space ↦ 0) ∈ initialClassT

  -- from DraftA:1323 (binder order `a, ν, T, s`), which is byte-identical to
  -- the already reconciled `BlowupDensity.T19.PeriodicDensityAPI.fixedInitialDensity`
  -- (`research/T19/Spec.lean:207-211`) copied above, so the seam with T19 needs
  -- no binder shuffling.  DraftB:1323 is the same `Prop` with `ν, T` first.
  /-- **Clause (i)**, `03-torus.tex:9`: for every fixed `a ∈ 𝓧`, the set
  `𝓑_{ν,a,T}` is dense in `𝓕` for the relative `L¹_tH^s_x` topology whenever
  `s < 1/2`.  This is `prop:density` (`:349-356`) read as an assertion of the
  theorem; it is literally
  `BlowupDensity.T19.PeriodicDensityAPI.fixedInitialDensity`.

  Exact quantifier order: `∀ a, a ∈ 𝓧 → ∀ ν, 0 < ν → ∀ T, 0 < T → ∀ s,`
  `s < 1/2 → RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)`.

  Non-vacuity: the conclusion is the registered positive-radius density predicate
  over the registered breakdown set — the witness must be an actual force of `𝓕`
  whose registered maximal lifespan is at most `T`. -/
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

  -- from DraftB:1342 (single biconditional, the R41 convention).  DraftA splits
  -- it into `zeroInitialDensity_subcritical` (DraftA:1336) and
  -- `zeroInitialDensity_only_if` (DraftA:1351); `.mp` / `.mpr` recover those.
  /-- **Clause (ii)**, `03-torus.tex:10-14`: for zero initial velocity,
  `𝓑⁰_{ν,T}` is dense in `𝓕` **if and only if** `s < 1/2`.  Both directions are
  kept under exactly the same hypotheses in a single biconditional — the shape of
  the registered whole-space `MainThresholdsAPI.zeroInitialDensityIff` — so
  equality of orders (`s = 1/2`) is included on the non-density side.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ s : ℝ,`
  `RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1/2`.

  Non-vacuity: the left side is the registered density predicate specialized to
  the concrete zero-datum breakdown set, so neither direction can be discharged
  by an unconstrained proposition; the right side is a strict inequality of
  reals, not a placeholder. -/
  zeroInitialDensityIff : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2

  -- from DraftB:1359 (`zeroInitialNonDensity`).  DraftA has the same `Prop` only
  -- as the free-standing `def nonDensityStatement` (DraftA:1374), not as a field
  -- of `MainTheoremAPI`.
  /-- `03-torus.tex:523`: the second of "the two assertions of the theorem", in
  the polarity in which `cor:nondensity` supplies it — non-density for zero
  initial velocity at every `s ≥ 1/2`.  Logically it is the contrapositive of the
  forward direction of `zeroInitialDensityIff`; it is kept as its own field
  because `:523` names it as an assertion of the theorem and because it is the
  clause a consumer inherits directly from `NonDensityAPI.nonDensity`.  The
  registered `MainThresholdsAPI` keeps only the biconditional
  (`RECONCILIATION.md` §3).

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ s, 1/2 ≤ s →`
  `¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)`.

  Non-vacuity: the negation is of the registered density predicate; it is refuted
  by an explicit reference force and radius, and `1/2 ≤ s` includes the critical
  order itself. -/
  zeroInitialNonDensity : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, 1 / 2 ≤ s →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

-- from DraftA:1361 (the conjunction of the two clause fields, so that the alias
-- is discharged by `⟨api.fixedInitialDensity, api.zeroInitialDensityIff⟩`) with
-- DraftB's biconditional for clause (ii).  DraftB:1368 binds `ν, T` outermost
-- and is the same `Prop` up to binder position.
/-- **`thm:main` in the paper's order, `03-torus.tex:6-16`.**  Clause (i)
followed by clause (ii)'s biconditional, under the `ν, T > 0` fixed at
`02-preliminaries.tex:38`.  Equals the conjunction of
`MainTheoremAPI.fixedInitialDensity` and
`MainTheoremAPI.zeroInitialDensityIff`. -/
def mainStatement : Prop :=
  (∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)) ∧
    (∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
      RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2)

/-! ## 3. What the assembly consumes

`03-torus.tex:523` is the whole proof of `thm:main`, and `:516` is the whole
proof of the disjointness in `cor:nondensity`.  The three signatures below record
that dependency as arrow types; no inhabitant is constructed here. -/

-- from DraftB:1386, with the **canonical** T20 record named rather than a copy
-- of it (`RECONCILIATION.md` §2).  DraftA:1384 threads a copied
-- `CriticalRegularityTAPI` as a structure parameter of `NonDensityAPI` instead.
/-- `03-torus.tex:511-516`: `cor:nondensity` is derived from `prop:critical`
alone — its constant `c`, that constant's positivity, and its global-regularity
conclusion.  No part of the construction spine (`thm:packet`, `thm:insertion`,
T19's `prop:density`) is used, exactly as `:380-381` says.

`NSFormalization.Section3.T20.CriticalRegularityTAPI` is the canonical T20
record; only its `c` appears here, and §5 shows how its `globalRegularity`
discharges `NonDensityAPI.criticalGlobalRegularity`. -/
def nonDensityOfCritical : Prop :=
  ∀ K : NSFormalization.Section3.T20.CriticalRegularityTAPI, NonDensityAPI K.c

-- from DraftB:1392.
/-- `03-torus.tex:523`: `thm:main` is `prop:density` plus `cor:nondensity` and
nothing else.  The constant `c` is bound universally because the theorem does not
mention it. -/
def mainOfDensityAndNonDensity : Prop :=
  ∀ c : ℝ,
    BlowupDensity.T19.PeriodicDensityAPI → NonDensityAPI c → MainTheoremAPI

-- from DraftB:1402 and DraftA:1384 (both drafts agree on the two-input shape).
/-- The two-input form asked for by the node: T19's density package and T20's
critical-regularity package assemble `thm:main`, through `nonDensityOfCritical`.
T19's other three structures (`MixedRegionAPI`, `StrongClosureAPI`,
`ProjectionAPI`) are corollaries of `prop:density` at `03-torus.tex:527-590` and
are **not** consumed here; neither are the packet and insertion contracts, which
T19 has already absorbed. -/
def mainOfInputs : Prop :=
  BlowupDensity.T19.PeriodicDensityAPI →
    NSFormalization.Section3.T20.CriticalRegularityTAPI →
      MainTheoremAPI

/-! ## 4. Seam check: the canonical T20 record discharges the registered field

`NonDensityAPI.criticalGlobalRegularity` is stated with the **registered**
`maximalLifespanT` (`Contracts/V1/TorusLocalTheory.lean`), while the canonical
`CriticalRegularityTAPI.globalRegularity` concludes with
`NSFormalization.Section3.T10.maximalLifespanT`.  These are not definitionally
equal — `ClassicalSolutionT` is a different inductive on the two sides
(`CLAUDE.md` structure exception) — but they are *propositionally* equal via
`BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq`
(`Bindings/TorusLocalTheory.lean:270`, proved through the fieldwise
`toContract`/`ofContract` conversions).  The hypotheses need no transport at all:
`forceClassT` and `forceSobolevENormT` are `rfl`-equal on the two sides
(`Bindings/TorusLocalTheory.lean:57,67`).

The `example` below is the whole bridge, and it is the answer to
`RECONCILIATION.md` §3 question (a): the T21 proof lane discharges
`criticalGlobalRegularity` by `rw [maximalLifespanT_eq]; exact K.globalRegularity …`.
It is a seam check, not a proof of any API field. -/

example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI)
    (ν : ℝ) (hν : 0 < ν) (g : SpaceTimeField) (hg : g ∈ forceClassT)
    (hsmall : forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (K.c * ν)) :
    maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  rw [BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq]
  exact K.globalRegularity ν hν g hg hsmall

end BlowupDensity.T21
