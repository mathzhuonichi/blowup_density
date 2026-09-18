import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.MainThresholds
import Contracts.V1.CompletedDensity
import Contracts.V1.Data
import Contracts.V1.MaximalPartial
import Contracts.V1.Correction

/-!
# T19: the density package on `T³`
# (`prop:density`, `cor:mixed`, `cor:closure`, `prop:projection`)

Reconciled, statement-only specification of the T19 node
(`collaboration/SECTION3_PLAN.md` §3, row T19), assembled from the two
double-blind drafts (lane 367 = draft A, lane 372 = draft B) under the lead's
`research/T19/RECONCILIATION.md`.  This file contains no proofs.  It renders,
clause by clause, the four results of the density subsection of
`paper/sections/03-torus.tex`:

* `PeriodicDensityAPI` — `prop:density`, density for each fixed initial velocity
  (`:349-368`);
* `MixedRegionAPI`     — `cor:mixed`, the sufficient mixed-norm region
  `3/p+2/q>3` (`:528-538`);
* `StrongClosureAPI`   — `cor:closure`, strong closure in energy and dissipation
  (`:540-561`);
* `ProjectionAPI`      — `prop:projection`, projection of extended singular data,
  quantifier order `∀a∃f` (`:564-590`).

## Reconciled bases (per structure)

Per `RECONCILIATION.md` §3: `PeriodicDensityAPI` → base **B**, `MixedRegionAPI`
→ base **B**, `StrongClosureAPI` → base **A**, `ProjectionAPI` → base **A**.
All four structures are **`Prop`-valued**: none of the four results introduces a
distinguished constant or datum (the packet/scaling/correction constants
`M, D, C_{p,q}, C_s` all live inside T18's `PeriodicInsertionAPI`, and the
smallness constant `c` inside T20's `prop:critical`; T19 only consumes their
conclusions), so every constructed force/family is bound existentially inside a
field.  This follows T24's data-free `Prop` precedent; it diverges from the
R41/R46 registry convention of `Type` (owner question §2 of the reconciliation).

## What T19 consumes, and what is *not* threaded

The proofs of all four results consume `thm:insertion` (T18) as a black box in
the regular-reference case and `prop:local` (T11) for the dichotomy on `T_max`.
T18's `PeriodicInsertionAPI` is reconciled but **unregistered**, and a registered
`Contracts/V1` file may import only `Contracts.*`; so — exactly as the registered
Section 4 counterparts `MainThresholdsAPI.regularReferenceApproximation`
(`Contracts/V1/MainThresholds.lean`) and
`CompletedDensityAPI.strongTrajectoryClosure` (`Contracts/V1/CompletedDensity.lean`)
restate insertion conclusions rather than reasoning inside the insertion record
— the regular-reference and closure fields here name the *conclusions* of
`thm:insertion` (`force ε ∈ forceClassT`, exact `maximalLifespanT = ofReal T`,
the `ClassicalSolutionT`, the closeness limits) in registered torus vocabulary.
The T18 record is **not** threaded (`RECONCILIATION.md` §3).  T20 (`prop:critical`)
is **not** consumed: it feeds `cor:nondensity` = node T21.

## Copy policy

Everything registered is imported and used by name, never copied
(`ClassicalSolutionT`, `maximalLifespanT`, `RegularThroughT`, `breakdownSetT`,
`RelativelyDenseT`, `forceClassT`, `initialClassT`, `forceSobolevENormT`,
`energyENormT`, `energyEssSupT`, `criticalOrder`, `alpha`,
`MaximalPartial.{limsupLeft,speedENorm}`).  Only two unregistered carriers —
`IsPeriodicLebesgueSlicePath` and `mixedLebesgueENormT`, needed to state
`cor:mixed` in the relative `L^q(0,∞;L^p(T³))` topology (only the whole-space
`Data.mixedLebesgueENorm` is registered) — are copied verbatim from
`research/T18/Spec.lean:395-410` into their historical namespace
`BlowupDensity.T15.Draft`.  Per the reconciliation, `alphaT` is **not** copied
(the registered `Contracts.V1.alpha` is used directly), and no honesty guard
(`MemMixedLebesgueT`/`MemForceSobolevT`) is copied (every closeness here is
strict `< r` or `Tendsto … (𝓝 0)`, self-guarding in `ℝ≥0∞`).  The paper's own
objects `RegularTrajectoryT`, `SingularTrajectoryT`, `extendedBreakdownSetT`,
`spaceTimeL2L2ENormT` (from A) and `RelativelyDenseMixedT` (from B) are restated
over registered vocabulary as local defs, not copies of any record.

The threshold is the torus value `s_c = 1/2` (`03-torus.tex:350`; the torus
fixes `q = 1`, `SECTION3_PLAN.md` §4).  Numerically `1/2 = criticalOrder 1`
(`Contracts/V1/Data.lean`), pinned by `PeriodicDensityAPI.thresholdValue`, but
the paper writes `s < 1/2` literally, so the density fields do too.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal Topology BigOperators

/- Copied verbatim from `research/T18/Spec.lean:395-410` (the
   `BlowupDensity.T15.Draft` mixed-Lebesgue torus carriers, themselves the T15
   layer); dependencies resolve through the registered `Contracts.V1.TorusData`
   / `Contracts.V1.Data` imports above.  `alphaT` is deliberately NOT copied —
   the registered `Contracts.V1.alpha` is used directly (`RECONCILIATION.md`
   §3). -/
namespace BlowupDensity.T15.Draft

open Set MeasureTheory
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- `03-torus.tex:129-133`: `G(t)` is the normalized-Haar `L^p(T³)`
slice of the periodic physical field. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- `03-torus.tex:129-133`: the torus
`L^q(0,∞;L^p(T³))` extended norm. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

end BlowupDensity.T15.Draft
/- end verbatim T15/T18 carrier copy -/

namespace BlowupDensity.T19

open BlowupDensity.T15.Draft

/-! ## 0. The paper's sets and norms, restated over registered vocabulary

These are the paper's own objects (`R_{a,T}`, `S_{a,T}`, `𝔅_{ν,T}`, the
`L²(0,T;L²)` norm, and the mixed-Lebesgue density predicate), stated over
registered classical-solution / lifespan / force / energy vocabulary.  They are
*not* stubs of any imported record. -/

/-- `03-torus.tex:541` `cor:closure`: `R_{a,T}`, the trajectories with initial
velocity `a` and force in `𝓕` smooth *through* `T` — i.e. the velocity of some
classical solution regular on `[0,T+δ)` for some `δ>0` (`RegularThroughT`). -/
def RegularTrajectoryT (ν : ℝ) (a : SpatialField) (T : ℝ) (u : SpaceTimeField) :
    Prop :=
  ∃ g : SpaceTimeField, g ∈ forceClassT ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a g (T + δ), w.velocity = u

/-- `03-torus.tex:542` `cor:closure`: `S_{a,T}`, the trajectories with initial
velocity `a`, force in `𝓕` smooth on `[0,T)` (a classical solution on the
horizon `T`), finite energy norm `E_T`, and unbounded maximum velocity at `T`.
Unboundedness is the registered ess-sup form
`limsupLeft T (t ↦ speedENorm (u(t,·))) = ⊤`
(`Contracts/V1/MaximalPartial.lean`). -/
def SingularTrajectoryT (ν : ℝ) (a : SpatialField) (T : ℝ) (u : SpaceTimeField) :
    Prop :=
  ∃ g : SpaceTimeField, g ∈ forceClassT ∧
    (∃ w : ClassicalSolutionT ν a g T, w.velocity = u) ∧
    energyENormT T u ≠ ⊤ ∧
    BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft T
        (fun t => BlowupDensity.Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => u (t, x))) = ⊤

/-- `03-torus.tex:565-568` `prop:projection`: the extended singular-data set
`𝔅_{ν,T} = {(a,f) ∈ 𝓧×𝓕 : T_max^ν(a,f) ≤ T}`. -/
def extendedBreakdownSetT (ν T : ℝ) : Set (SpatialField × SpaceTimeField) :=
  {p | p.1 ∈ initialClassT ∧ p.2 ∈ forceClassT ∧
    maximalLifespanT ν p.1 p.2 ≤ ENNReal.ofReal T}

/-- `03-torus.tex:558` `cor:closure`: the torus `L²(0,T;L²(T³))` extended norm,
the left-hand side of the time-embedding inequality `:556-560` used to identify
the `E_T` metric with the `L²_tH¹_x` sum norm. -/
def spaceTimeL2L2ENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (torusLift (fun x => z (t, x))) 2 periodicTorusMeasure) ^ (2 : ℝ))
    ^ ((2 : ℝ)⁻¹)

/-- `03-torus.tex:529-531` `cor:mixed`: relative density in the periodic
`L^q(0,∞;L^p(T³))` pseudometric — the exact mixed-norm analogue of the
registered `RelativelyDenseT` (`Contracts/V1/TorusLocalTheory.lean:226-229`),
built from the registered `breakdownSetT`/`forceClassT` and the copied honest
torus mixed norm `mixedLebesgueENormT`.  Not a stub for any imported record. -/
def RelativelyDenseMixedT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Y S : Set SpaceTimeField) : Prop :=
  ∀ g ∈ Y, ∀ r : ℝ≥0∞, 0 < r →
    ∃ f ∈ S,
      BlowupDensity.T15.Draft.mixedLebesgueENormT q p (fun z => f z - g z) < r

/-! ## 1. `prop:density` (`03-torus.tex:349-368`), base B -/

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

/-! ## 2. `cor:mixed` (`03-torus.tex:528-538`), base B -/

/-- **`cor:mixed` — a sufficient mixed-norm region,
`paper/sections/03-torus.tex:528-533`, proof `:534-536`, illustration `:538`.**

For fixed `a ∈ 𝓧`, `B_{ν,a,T}` is dense in `𝓕` for the relative
`L^q(0,∞;L^p(T³))` topology whenever `1≤p,q≤∞` and `3/p+2/q>3`.  `Prop`-valued
for the same reason as `prop:density`.  Base B (`RECONCILIATION.md` §3). -/
structure MixedRegionAPI : Prop where
  /-- `03-torus.tex:529-531`, `eq:mixedregion`, the corollary itself: for every
  fixed initial velocity the breakdown set is relatively dense in `𝓕` for the
  `L^q(0,∞;L^p(T³))` topology whenever `1≤p,q≤∞` and `3/p+2/q>3`.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T →`
  `∀ (p q : ℝ≥0∞) [Fact (1≤p)], 1≤q → 3<3/p.toReal+2/q.toReal →`
  `RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)`.  `[Fact (1≤p)]`
  supplies `1≤p`; `1≤q` is explicit; `p,q≤∞` are automatic in `ℝ≥0∞`; the `∞`
  endpoints are included exactly as `:531` (`toReal ⊤ = 0`).

  Non-vacuity: `RelativelyDenseMixedT` uses the honest torus mixed Bochner norm
  `mixedLebesgueENormT` (an `⨅` over strongly measurable `L^p(T³)`-slice paths,
  so a missing representative reports `⊤`, not a spurious small distance), and
  `< r` forces it finite, so the witness `f` is a real breakdown force whose
  mixed difference is genuinely small. -/
  mixedDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
          3 < 3 / p.toReal + 2 / q.toReal →
            RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)

  /-- `03-torus.tex:535-536`, the proof's arithmetic driver: on the region
  `3/p+2/q>3` (with `ℝ≥0∞.toReal ∞ = 0`), the scaling exponent
  `α(p,q) = alpha p q = -3+3/p.toReal+2/q.toReal` (registered
  `Contracts/V1/Correction.lean`) and its shift `α(p,q)+1` are both strictly
  positive — precisely the fact that makes both terms of
  `‖g_ε-g‖_{L^q_tL^p} ≤ C(ε^{α}+ε^{α+1})` (`eq:Fclose`) tend to zero.

  Exact quantifier order: `∀ p q : ℝ≥0∞, 3<3/p.toReal+2/q.toReal →`
  `0 < alpha p q ∧ 0 < alpha p q + 1`.

  Non-vacuity: both conjuncts are explicit strict inequalities on the registered
  exponent `alpha`; they turn the region hypothesis into the two exponent signs
  used in `eq:Fclose`, not a restatement of the region. -/
  mixedRegionArithmetic :
    ∀ p q : ℝ≥0∞, 3 < 3 / p.toReal + 2 / q.toReal →
      0 < BlowupDensity.Contracts.V1.alpha p q ∧
        0 < BlowupDensity.Contracts.V1.alpha p q + 1

  /-- `03-torus.tex:538`: the two named spaces the region contains,
  `L^1_tL^2_x` (`p=2, q=1`) and `L^2_tL^{4/3}_x` (`p=4/3, q=2`), instantiate
  `eq:mixedregion` — stated through the registered exponent at `ℝ≥0∞` points as
  `0 < α(2,1)` and `0 < α(4/3,2)` (equivalently `3/2+2>3` and `9/4+1>3`).

  Exact quantifier order: none; a conjunction of the two region positivities at
  the two displayed exponent pairs.

  Non-vacuity: two concrete strict inequalities of the registered rate exponent
  (`α(2,1)=1/2>0`, `α(4/3,2)=1/4>0`), the paper's explicit "the sufficient
  region includes …" sentence, instantiating the region predicate rather than
  floating as disconnected reals. -/
  regionExamples :
    0 < BlowupDensity.Contracts.V1.alpha 2 1 ∧
      0 < BlowupDensity.Contracts.V1.alpha (4 / 3) 2

/-- **`cor:mixed` in the paper's quantifier order, `03-torus.tex:529-531`.** -/
def mixedRegionStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
        3 < 3 / p.toReal + 2 / q.toReal →
          RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)

/-! ## 3. `cor:closure` (`03-torus.tex:540-561`), base A -/

/-- **`cor:closure` — strong closure in energy and dissipation,
`paper/sections/03-torus.tex:540-549`, proof `:552-561`.**

Fix `a ∈ 𝓧`.  The regular trajectories `R_{a,T}` lie in the `E_T`-closure of the
singular trajectories `S_{a,T}` (`eq:closure`), and every reference pair `(v,g)`
has approximants `(u_ε,g_ε)→(v,g)` in `E_T × L^1_tH^s_x` for `s<1/2`.
`Prop`-valued.  Base A, with B's `referenceFiniteEnergy` field added and B's
`history` clause dropped (`RECONCILIATION.md` §3). -/
structure StrongClosureAPI : Prop where
  /-- `03-torus.tex:556-560`, the norm identification behind `eq:closure`:
  `‖z‖_{L²(0,T;L²)} ≤ T^{1/2} ‖z‖_{L^∞(0,T;L²)}`.  Here the right side is the
  registered `energyEssSupT` (first summand of `E_T`) and the left the local
  `spaceTimeL2L2ENormT`; together with the shared gradient term this shows `E_T`
  and the `L²_tH^1_x` sum norm control each other, the equivalence "used in
  `eq:closure`" (`:561`).

  Exact quantifier order: `∀ T, 0<T → ∀ z`.

  Non-vacuity: a genuine `ℝ≥0∞` inequality relating two honest space-time norms,
  with the constant `T^{1/2} = Real.sqrt T`; not a tautology. -/
  energyTimeEmbedding :
    ∀ T : ℝ, 0 < T → ∀ z : SpaceTimeField,
      spaceTimeL2L2ENormT T z ≤
        ENNReal.ofReal (Real.sqrt T) * energyEssSupT T z

  /-- `03-torus.tex:543-545` `eq:closure`: `R_{a,T} ⊆ closure(S_{a,T})^{E_T}`.
  Rendered as the `ε`-approximation form of membership in the `E_T`-closure
  (exactly as `RelativelyDenseT` renders density, avoiding a `TopologicalSpace`
  instance on trajectory space): every regular trajectory is `E_T`-approximated
  by singular trajectories.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ u,`
  `RegularTrajectoryT ν a T u → ∀ r, 0<r → ∃ u', SingularTrajectoryT ∧ dist<r`.

  Non-vacuity: `u'` is a genuine singular trajectory (finite `E_T`, unbounded
  speed at `T`) and the distance is the registered `energyENormT` of the actual
  difference; `RegularTrajectoryT`/`SingularTrajectoryT` are the paper's `R`/`S`
  (`:541-542`) spelled over registered classical solutions. -/
  closureInEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
              energyENormT T (fun z => u z - u' z) < r

  /-- `03-torus.tex:546-549`, simultaneous pair convergence: for each reference
  pair `(v,g)` — `g∈𝓕` regular through `T` (a `ClassicalSolutionT ν a g (T+δ)`,
  `δ>0`), `v` its velocity — there are approximating pairs `(u_ε,g_ε)` with
  `u_ε` a singular trajectory (`g_ε∈𝓕`, lifespan exactly `T`, `u_ε` its velocity,
  finite `E_T`, blow-up at `T`) such that `u_ε→v` in `E_T` and `g_ε→g` in
  `L^1_tH^s_x` simultaneously for every fixed `s<1/2`.  Mirrors
  `CompletedDensityAPI.strongTrajectoryClosure`; B's `history` clause is dropped
  (a `thm:insertion` detail, not a `cor:closure` statement clause).

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ g, g∈𝓕 →`
  `∀ δ, 0<δ → ∀ reference : ClassicalSolutionT ν a g (T+δ) → ∃ ε₀, 0<ε₀ ∧`
  `∃ u f, (∀ε∈(0,ε₀): per-ε) ∧ (E_T limit) ∧ (∀ s<1/2, L^1_tH^s limit)`.

  Non-vacuity: the single family `(u,f)` witnesses both limits; each `u ε` is a
  `SingularTrajectoryT`, the two limits are of registered `ℝ≥0∞` norms along the
  nontrivial filter `𝓝[>]0`, and the reference velocity `v = reference.velocity`
  is an actual regular trajectory (so the pair really lies in `R_{a,T}`). -/
  simultaneousPairConvergence :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              ∃ ε₀ : ℝ, 0 < ε₀ ∧
                ∃ u f : ℝ → SpaceTimeField,
                  (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                    f ε ∈ forceClassT ∧
                    maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                    (∃ w : ClassicalSolutionT ν a (f ε) T, w.velocity = u ε) ∧
                    SingularTrajectoryT ν a T (u ε)) ∧
                  Tendsto
                    (fun ε : ℝ =>
                      energyENormT T (fun z => u ε z - reference.velocity z))
                    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) ∧
                  (∀ s : ℝ, s < 1 / 2 →
                    Tendsto
                      (fun ε : ℝ => forceSobolevENormT 1 s (fun z => f ε z - g z))
                      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)))

  /-- `03-torus.tex:554`: the reference itself has finite `E_T` energy — it is
  smooth through `T` (a classical solution on `[0,T+δ)`, `δ>0`), hence bounded
  on the compact `[0,T]×T³`.  This anchors the `E_T` limit of
  `simultaneousPairConvergence` in a finite-distance ambient space.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ g, g∈𝓕 →`
  `∀ δ, 0<δ → ∀ reference : ClassicalSolutionT ν a g (T+δ),`
  `energyENormT T reference.velocity < ⊤`.

  Non-vacuity: a strict finiteness in `ℝ≥0∞` of the registered energy norm of an
  actual solution velocity, not a vacuous bound. -/
  referenceFiniteEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              energyENormT T reference.velocity < ⊤

/-- **`cor:closure` `eq:closure` in the paper's quantifier order,
`03-torus.tex:543-545`.**  The `E_T`-closure inclusion `R_{a,T} ⊆ S̄_{a,T}`. -/
def strongClosureStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
        ∀ r : ℝ≥0∞, 0 < r →
          ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
            energyENormT T (fun z => u z - u' z) < r

/-! ## 4. `prop:projection` (`03-torus.tex:564-590`), base A -/

/-- **`prop:projection` — projection of extended singular data,
`paper/sections/03-torus.tex:564-571`, proof `:573-576`, remarks `:579-590`.**

`𝔅_{ν,T} = {(a,f)∈𝓧×𝓕 : T_max^ν(a,f) ≤ T}` is dense (for `s<1/2`) in the product
of any topology on `𝓧` with the relative `L^1_tH^s_x` topology on `𝓕`; its
projection onto `𝓧` is all of `𝓧`; the `a=0` subfamily projects to `{0}`.  The
quantifier order is `∀a∃f` (`:579`).  `Prop`-valued.  Base A
(`RECONCILIATION.md` §3). -/
structure ProjectionAPI : Prop where
  /-- `03-torus.tex:570,573-575`, density in the product topology.  A basic
  product neighborhood of `(a,g)` is `U×V` with `U` any `𝓧`-neighborhood of `a`
  and `V` an `L^1_tH^s_x` ball; since `a∈U` always (`:574`), the paper keeps the
  same `a` and (by `prop:density`) picks `f∈V` with `T_max^ν(a,f)≤T`, i.e.
  `(a,f)∈𝔅_{ν,T}∩(U×V)`.  Rendered by keeping the initial datum fixed at `a`
  (its own point lies in every topology's neighborhood, discharging "any topology
  on `𝓧`") and approximating only the force factor.

  Exact quantifier order: `∀ ν, 0<ν → ∀ T, 0<T → ∀ s, s<1/2 → ∀ a, a∈𝓧 →`
  `∀ g, g∈𝓕 → ∀ r, 0<r → ∃ f`.

  Non-vacuity: the produced pair `(a,f)` lies in `extendedBreakdownSetT ν T`
  (so `a∈𝓧`, `f∈𝓕`, `T_max≤T`) and the force distance is the registered
  `forceSobolevENormT`, strictly below `r`. -/
  extendedProductDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        ∀ a : SpatialField, a ∈ initialClassT →
          ∀ g : SpaceTimeField, g ∈ forceClassT →
            ∀ r : ℝ≥0∞, 0 < r →
              ∃ f : SpaceTimeField,
                (a, f) ∈ extendedBreakdownSetT ν T ∧
                  forceSobolevENormT 1 s (fun z => f z - g z) < r

  /-- `03-torus.tex:570,579`, "its projection onto `𝓧` is all of `𝓧`", the
  `∀a∃f` statement (`:579-580`): the image of `𝔅_{ν,T}` under `Prod.fst` is
  exactly `𝓧 = initialClassT`.  `⊆` is by construction (`𝔅 ⊆ 𝓧×𝓕`); `⊇` is the
  content — applying `prop:density` with any fixed `g` and radius gives at least
  one singular force over each `a` (`:576`).

  Exact quantifier order: `∀ ν, 0<ν → ∀ T, 0<T →` set equality.

  Non-vacuity: the `⊇` inclusion of the image equality asserts, for every
  `a∈𝓧`, existence of `f` with `(a,f)∈𝔅_{ν,T}` — the genuine `∀a∃f`, not a
  vacuous image. -/
  projectionOntoInitialData :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst '' (extendedBreakdownSetT ν T) = initialClassT

  /-- `03-torus.tex:571`, "the family obtained while requiring `a=0` projects
  instead to the singleton `{0}`": the image under `Prod.fst` of the `a=0`
  subfamily of `𝔅_{ν,T}` equals `{0}`.  `⊆` is the constraint; `⊇` requires a
  singular force over `a=0` (`0∈𝓧`, `prop:density` at `a=0`).  This is the
  contrast the paper draws at `:586` with the `∀a∃f` surjectivity (`{0}` is not
  dense in a nontrivial normed `𝓧`).

  Exact quantifier order: `∀ ν, 0<ν → ∀ T, 0<T →` set equality.

  Non-vacuity: the `⊇` direction forces the `a=0` subfamily nonempty (a real
  singular force over `0`), so the projection is the nonempty singleton `{0}`,
  not the empty set. -/
  zeroInitialProjection :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst ''
          {p : SpatialField × SpaceTimeField |
            p ∈ extendedBreakdownSetT ν T ∧ p.1 = (fun _ => 0)} =
        {(fun _ => 0 : SpatialField)}

/-- **`prop:projection` in the paper's quantifier order, `03-torus.tex:565-571`.**
Density of `𝔅_{ν,T}` in the product topology (force factor, initial datum kept)
together with the full projection onto `𝓧`. -/
def projectionStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    (∀ s : ℝ, s < 1 / 2 →
      ∀ a : SpatialField, a ∈ initialClassT →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ f : SpaceTimeField,
              (a, f) ∈ extendedBreakdownSetT ν T ∧
                forceSobolevENormT 1 s (fun z => f z - g z) < r) ∧
    Prod.fst '' (extendedBreakdownSetT ν T) = initialClassT

end BlowupDensity.T19
