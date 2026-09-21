import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.GradientL6
import Contracts.V1.MainThresholds
import Contracts.V1.CompletedDensity
import Contracts.V1.Packet
import Contracts.V1.PacketImport
import Contracts.V1.CriticalRegularity
import Contracts.V1.MaximalPartial
import Contracts.V1.Data

noncomputable section

/- copied verbatim from research/T19/Spec.lean:192-518; canonical T19 blocks. -/
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

open BlowupDensity.Contracts.V1.TorusLocalTheory
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

/- copied verbatim from research/T20/Spec.lean:613-890; canonical T12 blocks, with registered T10/T11 vocabulary imported above. -/
namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal BigOperators
/-! ## Scalar datum and physical membership classes -/

/-- `01-introduction.tex:83-84`: `A` is the order-`s` weighted Fourier
datum of a real scalar periodic field.  This is the scalar mirror of T10's
`IsPeriodicDatum`, including its periodicity and Haar-integrability
conjuncts; the exact coefficient quantifier is `∀ k : PeriodicFrequency`. -/
def IsPeriodicScalarDatum (s : ℝ) (z : Space → ℝ)
    (A : PeriodicScalarData) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧
    ∀ k : PeriodicFrequency,
      A k = (periodicFrequencyWeight k) ^ (s / 2) •
        periodicFourierCoeff (fun x ↦ ((z x : ℝ) : ℂ)) k

/-- `01-introduction.tex:83-84`: the total scalar `H^s(T³)` extended norm,
defined exactly like T10's vector norm.  The empty infimum is `⊤`. -/
def periodicScalarSobolevENorm (s : ℝ) (z : Space → ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicScalarData // IsPeriodicScalarDatum s z A}, ‖A.1‖ₑ

/-- `appendix-a-local-theory.tex:8-12`: scalar membership in periodic
`H^m`.  The conjunct order is periodicity, physical `L²`, then finiteness of
the total scalar datum norm. -/
def MemPeriodicHmScalar (m : ℕ) (z : Space → ℝ) : Prop :=
  IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure ∧
    periodicScalarSobolevENorm (m : ℝ) z ≠ ⊤

/-- `appendix-a-local-theory.tex:8-12`: vector membership in periodic
`H^m`.  The conjunct order is periodicity, physical `L²`, then finiteness of
T10's total vector datum norm. -/
def MemPeriodicHmVector (m : ℕ) (z : SpatialField) : Prop :=
  IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure ∧
    periodicSobolevENorm (m : ℝ) z ≠ ⊤

/-- `appendix-b-embeddings.tex:20-22,26-27`: a physical mean-zero periodic
representative with finite displayed homogeneous norm.  The exact conjunct
order is periodicity, physical `L²`, physical Haar mean zero, then finiteness. -/
def MemPeriodicHomogeneous (s : ℝ) (z : SpatialField) : Prop :=
  IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure ∧
    IsMeanZeroT z ∧ periodicHomogeneousENorm s z ≠ ⊤

/-- `appendix-b-embeddings.tex:34-37`: the smooth periodic fields used by the
article's derivative displays.  Smoothness precedes physical periodicity. -/
def SmoothPeriodicT (z : SpatialField) : Prop :=
  ContDiff ℝ ∞ z ∧ IsPeriodicSpatial z

/-- `01-introduction.tex:104`: the physical `L^p(T³)` extended norm of any
normed additive target, against normalized Haar measure. -/
def periodicLpENorm {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (z : Space → E) : ℝ≥0∞ :=
  eLpNorm (torusLift z) p periodicTorusMeasure

/-! ## Registered derivative spelling and the periodic Lambda graph -/

/-- `appendix-b-embeddings.tex:34-37` and `03-torus.tex:467-477`: the
time-independent lift used to reuse the registered spatial operators.
Copied token-for-token from `Contracts/V1/GradientL6.lean:78`. -/
def lift (v : SpatialField) : SpaceTimeField := fun z => v z.2

/-- `appendix-b-embeddings.tex:30-32,97-100`: the physical Frobenius gradient
tensor.  Copied token-for-token from
`Contracts/V1/GradientL6.lean:89-90`. -/
def gradientTensor (v : SpatialField) : Space → WithLp 2 (Fin 3 → Space) :=
  fun x => spatialGradient (lift v) 0 x

/-- `appendix-b-embeddings.tex:32,97-100` and `03-torus.tex:467-477`: the
componentwise spatial Laplacian.  Copied token-for-token from
`Contracts/V1/GradientL6.lean:94-95`. -/
def laplacian (v : SpatialField) : SpatialField :=
  fun x => spatialLaplacian (lift v) 0 x

/-- `appendix-b-embeddings.tex:8-9,97`: `Lv` is the chosen smooth periodic
physical representative of `Λv`, fixed coefficientwise by the unit-torus
multiplier `2π|k| = sqrt(4π²|k|²)`.  The exact quantifier order after the
smoothness conjunct is component, then lattice frequency. -/
def IsPeriodicLambda (v Lv : SpatialField) : Prop :=
  SmoothPeriodicT Lv ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFourierCoeff (fun x ↦ ((Lv x i : ℝ) : ℂ)) k =
        Real.sqrt (periodicAngularFrequencySq k) *
          periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k

/-! ## Reconciled Type-valued API -/

/-- The torus halves of Lemma A.1 and Lemma B.1, together with the mean-zero
order-two comparison used by Proposition 3.7.  Constants are data fields of
this Type-valued structure and therefore precede every field they control
(`appendix-b-embeddings.tex:109-110`). -/
structure MeanZeroSobolevCalculusAPI where
  /-- `appendix-a-local-theory.tex:8-11`: the tame-product constant family.
  Exact quantifier order: the family is fixed as structure data before `m`,
  the lower-bound proof, and both scalar factors.
  Non-vacuity: `Cproduct_pos` below forces every used value to be positive. -/
  Cproduct : ℕ → ℝ

  /-- `appendix-a-local-theory.tex:8-11`: positivity of the tame-product
  constants.  Exact quantifier order: `∀ m : ℕ`.
  Non-vacuity: this constrains the preceding data family at every order rather
  than permitting a zero constant. -/
  Cproduct_pos : ∀ m : ℕ, 0 < Cproduct m

  /-- `appendix-a-local-theory.tex:12`: the `H²(T³) → L∞(T³)` constant,
  fixed before the vector field.
  Non-vacuity: `Cinfty_pos` below forces this concrete datum to be positive. -/
  Cinfty : ℝ

  /-- `appendix-a-local-theory.tex:12`: positivity of `Cinfty`; there are no
  later quantifiers.
  Non-vacuity: it rules out a zero embedding constant. -/
  Cinfty_pos : 0 < Cinfty

  /-- `appendix-b-embeddings.tex:20-22,26-29`: the critical
  `Ḣ^(1/2)(T³) → L³(T³)` constant, fixed before the field.
  Non-vacuity: `C₀Half_pos` forces a positive datum. -/
  C₀Half : ℝ

  /-- `appendix-b-embeddings.tex:12-17,20-22`: positivity of the half-order
  critical constant; there are no later quantifiers.
  Non-vacuity: it constrains the actual constant used by
  `velocityCriticalL3`. -/
  C₀Half_pos : 0 < C₀Half

  /-- `appendix-b-embeddings.tex:26-31`: the one constant for the displayed
  sum of the gradient and Lambda `L³` norms, fixed before both fields.
  Non-vacuity: `C₀ThreeHalves_pos` forces a positive datum. -/
  C₀ThreeHalves : ℝ

  /-- `appendix-b-embeddings.tex:12-13,26-31`: positivity of the
  three-halves constant; there are no later quantifiers.
  Non-vacuity: it constrains the constant used in the combined display. -/
  C₀ThreeHalves_pos : 0 < C₀ThreeHalves

  /-- `appendix-b-embeddings.tex:26-32`: the gradient-`L⁶` constant, fixed
  before the field.
  Non-vacuity: `Csix_pos` forces the registered-spelling constant to be
  positive. -/
  Csix : ℝ

  /-- `appendix-b-embeddings.tex:12-13,26-32`: positivity of `Csix`; there
  are no later quantifiers.
  Non-vacuity: it rules out a zero right-hand coefficient. -/
  Csix_pos : 0 < Csix

  /-- `03-torus.tex:490-500`: the mean-zero `H²`/Laplacian comparison
  constant, fixed before the field.
  Non-vacuity: `CHtwo_pos` forces a positive datum. -/
  CHtwo : ℝ

  /-- `03-torus.tex:490-500`: positivity of `CHtwo`; there are no later
  quantifiers.
  Non-vacuity: it constrains the actual continuation constant. -/
  CHtwo_pos : 0 < CHtwo

  /-- `02-preliminaries.tex:50-54` and
  `appendix-b-embeddings.tex:85-90`: the spectral-gap constant family,
  fixed before the nonnegative order and field.
  Non-vacuity: `Cgap_pos` forces every value used at `0 ≤ s` to be positive. -/
  Cgap : ℝ → ℝ

  /-- `02-preliminaries.tex:50-54` and
  `appendix-b-embeddings.tex:85-90`: positivity of the gap constant.
  Exact quantifier order: `∀ s : ℝ`, then `0 ≤ s`.
  Non-vacuity: the guard is exactly the guard of `spectralGap`, so every
  applied constant is genuinely positive. -/
  Cgap_pos : ∀ s : ℝ, 0 ≤ s → 0 < Cgap s

  /-- `appendix-a-local-theory.tex:8-11`, `eq:Rproduct`, torus half.
  Exact quantifier order: `m`, `2 ≤ m`, scalar `a`, scalar `b`, membership
  of `a`, then membership of `b`; `Cproduct m` was fixed first.
  Non-vacuity: the two `MemPeriodicHmScalar` hypotheses supply genuine
  periodic `L²` representatives with finite totalized `H^m` norms. -/
  tameProduct :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : Space → ℝ,
      MemPeriodicHmScalar m a → MemPeriodicHmScalar m b →
        periodicScalarSobolevENorm (m : ℝ) (fun x ↦ a x * b x) ≤
          ENNReal.ofReal (Cproduct m) *
            (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (m : ℝ) b +
              periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (m : ℝ) a)

  /-- `appendix-a-local-theory.tex:8-12`, the torus
  `H² → L∞` clause.  Exact quantifier order: vector `v`, then its order-two
  membership; no mean-zero hypothesis is inserted.
  Non-vacuity: `MemPeriodicHmVector 2 v` supplies a periodic `L²`
  representative and a finite totalized `H²` norm. -/
  boundedRepresentative :
    ∀ v : SpatialField, MemPeriodicHmVector 2 v →
      periodicLpENorm ⊤ v ≤
        ENNReal.ofReal Cinfty * periodicSobolevENorm 2 v

  /-- `appendix-b-embeddings.tex:20-22,26-29`: the mean-zero torus
  `Ḣ^(1/2) → L³` clause.  Exact quantifier order: vector `v`, then the bundled
  homogeneous membership.
  Non-vacuity: `MemPeriodicHomogeneous (1 / 2) v` supplies periodicity, a
  physical `L²` representative, zero Haar mean, and a finite homogeneous
  datum norm. -/
  velocityCriticalL3 :
    ∀ v : SpatialField, MemPeriodicHomogeneous (1 / 2) v →
      periodicLpENorm 3 v ≤
        ENNReal.ofReal C₀Half * periodicHomogeneousENorm (1 / 2) v

  /-- `appendix-b-embeddings.tex:8-9,26-31,97`: every smooth periodic field
  has a chosen physical representative of `Λv`.
  Exact quantifier order: vector `v`, smooth-periodic hypothesis, then
  `∃ Lv : SpatialField`.
  Non-vacuity: the zero field witnesses the hypothesis, while the existential
  conclusion supplies the representative required by the next field. -/
  lambda_exists :
    ∀ v : SpatialField, SmoothPeriodicT v →
      ∃ Lv : SpatialField, IsPeriodicLambda v Lv

  /-- `appendix-a-local-theory.tex:22-26` and
  `appendix-b-embeddings.tex:26-31`: the single displayed order-three-halves
  sum inequality.  Exact quantifier order: `v`, `Lv`, smooth periodicity of
  `v`, bundled order-three-halves membership, then the Lambda graph.
  Non-vacuity: the preceding `lambda_exists` field supplies an `Lv` witness
  for every `SmoothPeriodicT v`; `MemPeriodicHomogeneous (3 / 2) v` supplies
  the finite right-hand norm. -/
  gradientLambdaCriticalL3 :
    ∀ (v Lv : SpatialField), SmoothPeriodicT v →
      MemPeriodicHomogeneous (3 / 2) v → IsPeriodicLambda v Lv →
        periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
          ENNReal.ofReal C₀ThreeHalves *
            periodicHomogeneousENorm (3 / 2) v

  /-- `appendix-b-embeddings.tex:26-32`, used at
  `03-torus.tex:467-477`: the paper-literal mean-zero periodic
  `‖∇v‖₆ ≤ C‖Δv‖₂` clause.  Exact quantifier order: `v`, smooth periodicity,
  then physical zero mean.
  Non-vacuity: the zero field satisfies both hypotheses, while
  `SmoothPeriodicT v` supplies the classical gradient and Laplacian fields;
  the mean-zero hypothesis is retained even though derivatives kill constants. -/
  gradientLSix :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)

  /-- `03-torus.tex:490-500`: the mean-zero comparison used by continuation.
  Exact quantifier order: `v`, smooth periodicity, then physical zero mean.
  Non-vacuity: the zero field witnesses the hypotheses, and for every such
  field the conclusion compares T10's concrete total `H²` norm with the
  registered-spelling classical Laplacian norm. -/
  hTwo_le_laplacian :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicSobolevENorm 2 v ≤
        ENNReal.ofReal CHtwo * periodicLpENorm 2 (laplacian v)

  /-- `02-preliminaries.tex:50-54` and
  `appendix-b-embeddings.tex:85-90`: the spectral-gap direction of the
  mean-zero norm equivalence.  Exact quantifier order: real `s`, proof
  `0 ≤ s`, vector `v`, then bundled homogeneous membership.
  Non-vacuity: `MemPeriodicHomogeneous s v` supplies zero mean and a finite
  homogeneous datum norm, and hence excludes the empty-witness `⊤` case on
  the right. -/
  spectralGap :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (Cgap s) * periodicHomogeneousENorm s v

  /-- `02-preliminaries.tex:50-54`: the converse direction needed for the
  stated equivalence of homogeneous and inhomogeneous norms.
  Exact quantifier order: real `s`, proof `0 ≤ s`, vector `v`, then bundled
  homogeneous membership.
  Non-vacuity: `MemPeriodicHomogeneous s v` supplies a genuine mean-zero
  periodic `L²` representative with finite homogeneous datum; the conclusion
  fixes the converse constant to exactly one. -/
  homogeneous_le_sobolev :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicHomogeneousENorm s v ≤ periodicSobolevENorm s v

end NSFormalization.Section3.T12

/- copied verbatim from formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:29-376 (canonical T20-specific declarations and `CriticalRegularityTAPI`; support spelling copied from research/T20/Spec.lean). -/
namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators

/-! ## 1. The untranslated mean reduction -/

/-- `03-torus.tex:395-405`: for the zero initial datum, the data-defined mean
path `m(t) = ∫₀ᵗ meanT(g(s)) ds`.  This is T11's `galileanMeanT` without
performing the Galilean spatial translation. -/
def meanPathT (g : SpaceTimeField) (t : ℝ) : Space :=
  galileanMeanT (fun _ : Space ↦ 0) g t

/-- `03-torus.tex:395-401`: the untranslated mean-free velocity
`v(t,x) = u(t,x) - m(t)`. -/
def meanFreeVelocity (g u : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ u q - meanPathT g q.1

/-- `03-torus.tex:397-401`: the mean-free force
`h(t,x) = g(t,x) - meanT(g(t,·))`. -/
def meanFreeForce (g : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ g q - forceMeanT g q.1

/-- `03-torus.tex:408-411`: the constant transport `(m(t)·∇)v`, written
as the spatial Fréchet derivative of `v(t,·)` applied to `m(t)`. -/
def constantTransportT (m : ℝ → Space) (v : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ spatialDerivative v q.1 q.2 (m q.1)

/-- `03-torus.tex:411`: the fixed-time operator `z ↦ (m·∇)z`, used
to state skew-adjointness and commutation with `Λ` without arbitrary values in
the time coordinate. -/
def constantTransportSpatialT (m : Space) (v : SpatialField) : SpatialField :=
  fun x ↦ spatialDerivative (fun q ↦ v q.2) 0 x m

/-- `03-torus.tex:404-405`: the extended-valued integral
`∫₀ᵗ |meanT(g(s))| ds`; unlike a totalized real integral, failure of
measurability or integrability cannot turn this quantity into a junk zero. -/
def meanForceIntegralT (g : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal ‖forceMeanT g s‖

/-! ## 2. Critical and continuation quantities -/

/-- `03-torus.tex:414-418`: `y(t)=‖v(t)‖_{Ḣ^(1/2)}` in the registered
mean-zero coefficient realization. -/
def criticalY (v : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (1 / 2) (fun x ↦ v (t, x))

/-- `03-torus.tex:414-418`: `z(t)=‖v(t)‖_{Ḣ^(3/2)}` in the registered
mean-zero coefficient realization. -/
def criticalZ (v : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (3 / 2) (fun x ↦ v (t, x))

/-- `03-torus.tex:414-418`: `b(t)=‖h(t)‖_{Ḣ^(1/2)}`. -/
def criticalB (h : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (1 / 2) (fun x ↦ h (t, x))

/-- `03-torus.tex:441-444` (`eq:bintegral`): the proof's full-time
`B = ∫₀∞ b(t) dt`, kept in `ℝ≥0∞` so divergence is `⊤`. -/
def criticalBIntegral (h : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t, criticalB h t ∂forceTimeMeasure

/-- `03-torus.tex:383-389`: the critical inhomogeneous force size
`ρ = ‖g‖_{L¹(0,∞;H^(1/2))}`. -/
def criticalRho (g : SpaceTimeField) : ℝ≥0∞ :=
  forceSobolevENormT 1 (1 / 2) g

/-- `03-torus.tex:482-484`: `‖∇v‖²₂`, expressed through T12's
registered-spelling gradient tensor.  Its uses below explicitly assert that
the extended norm is finite before applying `toReal`. -/
def gradientSqT (v : SpatialField) : ℝ :=
  (periodicLpENorm 2 (gradientTensor v)).toReal ^ 2

/-- `03-torus.tex:468-484`: `‖Δv‖²₂`, expressed through T12's
registered-spelling componentwise Laplacian. -/
def laplacianSqT (v : SpatialField) : ℝ :=
  (periodicLpENorm 2 (laplacian v)).toReal ^ 2

/-- `03-torus.tex:479-488`: `‖h‖²₂` on the normalized unit torus. -/
def lTwoSqT (h : SpatialField) : ℝ :=
  (periodicLpENorm 2 h).toReal ^ 2

/-- `03-torus.tex:488-500`: the full positive-time integral
`∫₀∞ ‖h(t)‖²₂ dt`, with divergence represented by `⊤`. -/
def meanFreeForceLTwoSqIntegral (h : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t, (periodicLpENorm 2 (fun x ↦ h (t, x))) ^ (2 : ℝ) ∂forceTimeMeasure

/-- `03-torus.tex:494-500`: the right-hand integrand in the orthogonal
constant/mean-zero `H²` decomposition of `u`. -/
def meanModeCriterionIntegral (S : ℝ) (g u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S,
    ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ) +
      periodicSobolevENorm 2 (fun x ↦ meanFreeVelocity g u (t, x)) ^ (2 : ℝ)

/-- `03-torus.tex:411`: the real `L²(T³)` pairing used to state
skew-adjointness of constant transport.  Its API field below carries explicit
integrability hypotheses for both scalar integrands. -/
def periodicPairing (v w : SpatialField) : ℝ :=
  ∫ y : PeriodicTorus,
    (inner ℝ (torusLift v y) (torusLift w y) : ℝ) ∂periodicTorusMeasure

/-! ## 3. Proposition 3.7 and its displayed proof estimates -/

/-- Proposition `prop:critical` together with the named estimates in its
proof (`03-torus.tex:383-503`).  The interface is indexed by the binding T11
local/continuation/mean-reduction packages and the binding T12 calculus
package, making the DAG dependencies explicit without copying their facts as
new T20 fields.  It is **Type-valued** because the universal smallness radius
and the three absolute estimate constants are mathematical data selected
before every viscosity, force, and solution.  Their positivity and the two
bootstrap shrinkings prevent vacuous thresholds.

The estimates are stated for the untranslated field `v=u-m`; hence
`meanFreeEquation` retains `constantTransportT`.  Every occurrence of a
totalized norm is protected collectively by `reductionRegular`, while every
`toReal` use has an explicit `≠ ⊤` conclusion there. -/
structure CriticalRegularityTAPI : Type where
  /-- `03-torus.tex:383-387`: the universal smallness constant, selected
  before `ν` and `g`.
  Exact quantifier order: dependency packages first, then this constant,
  before every viscosity and force in the theorem fields.
  Non-vacuity: `hc` below forces a genuinely positive ball. -/
  c : ℝ

  /-- `03-torus.tex:383-387`: positivity of the universal smallness constant.
  Exact quantifier order: there are no later parameters.
  Non-vacuity: with `ν>0`, `ENNReal.ofReal (c*ν)` is positive. -/
  hc : 0 < c

  /-- `03-torus.tex:426-440`: the absolute constant in the critical
  trilinear estimate, fixed before all PDE data.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `C₀_pos` excludes the zero-constant trap. -/
  C₀ : ℝ

  /-- `03-torus.tex:426-440`: positivity of `C₀`.
  Exact quantifier order: no later parameters.
  Non-vacuity: the bootstrap level `ν/(2*C₀)` is meaningful. -/
  C₀_pos : 0 < C₀

  /-- `03-torus.tex:467-484`: the absolute coefficient of `y‖Δv‖²₂`
  in the `H¹` convection estimate, fixed before all PDE data.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `C₁_pos` below rules out zero. -/
  C₁ : ℝ

  /-- `03-torus.tex:467-484`: positivity of the `H¹` convection constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: the second bootstrap shrinking is therefore genuine. -/
  C₁_pos : 0 < C₁

  /-- `03-torus.tex:479-484`: the absolute constant after Young's inequality
  in `eq:H1energy`.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `CH1_pos` below prevents a zero right-hand coefficient. -/
  CH1 : ℝ

  /-- `03-torus.tex:479-484`: positivity of the `H¹` energy constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: this constrains the actual constant used in `hOneEnergy`. -/
  CH1_pos : 0 < CH1

  /-- `03-torus.tex:492-500`: the absolute constant in the assembled
  squared-`H²` continuation bound.
  Exact quantifier order: it is structure data before `ν,g,T,w,S`.
  Non-vacuity: `hCcriterion` below forces it to be positive. -/
  Ccriterion : ℝ

  /-- `03-torus.tex:492-500`: positivity of the continuation constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: the finite bound in `continuationBound` is quantitative. -/
  hCcriterion : 0 < Ccriterion

  /-- `03-torus.tex:457`: the first required shrinking
  `c < 1/(4 C₀)`.
  Exact quantifier order: constants were selected first.
  Non-vacuity: together with positivity it gives a nonempty, absorbing
  bootstrap regime. -/
  c_lt_C₀ : c < 1 / (4 * C₀)

  /-- `03-torus.tex:477-480`: the second required shrinking
  `c < 1/(4 C₁)`.
  Exact quantifier order: constants were selected first.
  Non-vacuity: this is the stated absorption gate for `eq:H1energy`. -/
  c_lt_C₁ : c < 1 / (4 * C₁)

  reductionRegular : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ico (0 : ℝ) T,
          let v := fun x ↦ meanFreeVelocity g w.velocity (t, x)
          let h := fun x ↦ meanFreeForce g (t, x)
          IsMeanZeroT v ∧ SmoothPeriodicT v ∧
            MemPeriodicHomogeneous (1 / 2) v ∧
            MemPeriodicHomogeneous (3 / 2) v ∧
            MemPeriodicHmVector 2 v ∧
            IsMeanZeroT h ∧ SmoothPeriodicT h ∧
            MemPeriodicHomogeneous (1 / 2) h ∧
            periodicLpENorm 2 h ≠ ⊤ ∧
            periodicLpENorm 2 (gradientTensor v) ≠ ⊤ ∧
            periodicLpENorm 2 (laplacian v) ≠ ⊤

  meanBound : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal ‖meanPathT g t‖ ≤ meanForceIntegralT g t ∧
        meanForceIntegralT g t ≤ criticalRho g

  /-- `03-torus.tex:407-410`, `eq:meanfree`: the untranslated mean-free field
  solves
  `∂ₜv+(v·∇)v+(m·∇)v-νΔv+∇p=h`.
  Exact quantifier order: `ν,hν,g,hg,T,w,t,ht,x`.
  Non-vacuity: this is a pointwise vector equation for the explicit `v`, `m`,
  `h`, and the normalized pressure of a full classical solution. -/
  meanFreeEquation : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
          temporalDerivative (meanFreeVelocity g w.velocity) t x +
              advection (meanFreeVelocity g w.velocity) t x +
              constantTransportT (meanPathT g)
                (meanFreeVelocity g w.velocity) (t, x) -
              ν • spatialLaplacian (meanFreeVelocity g w.velocity) t x +
              pressureGradient w.pressure t x =
            meanFreeForce g (t, x)

  /-- `03-torus.tex:411`: for fixed `m`, `(m·∇)` is skew-adjoint in
  periodic `L²`.
  Exact quantifier order: `m,v,w`, smooth-periodic hypotheses, followed by
  integrability of the two concrete pairing integrands.
  Non-vacuity: the conclusion is an equality of actual torus integrals; the
  integrability premises rule out Bochner-integral junk zeros. -/
  constantTransportSkew : ∀ (m : Space) (v w : SpatialField),
    SmoothPeriodicT v → SmoothPeriodicT w →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift (constantTransportSpatialT m v) y)
            (torusLift w y) : ℝ)) periodicTorusMeasure →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift v y)
            (torusLift (constantTransportSpatialT m w) y) : ℝ))
        periodicTorusMeasure →
        periodicPairing (constantTransportSpatialT m v) w =
          -periodicPairing v (constantTransportSpatialT m w)

  /-- `03-torus.tex:411`: constant transport commutes with the Fourier
  multiplier `Λ`.
  Exact quantifier order: `m,v,Lv`, smooth periodicity, then the T12 Lambda
  graph.
  Non-vacuity: the conclusion is the same concrete coefficientwise Lambda
  graph for the two transported physical fields. -/
  constantTransportCommutesLambda :
    ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
      IsPeriodicLambda v Lv →
        IsPeriodicLambda (constantTransportSpatialT m v)
          (constantTransportSpatialT m Lv)

  /-- `03-torus.tex:420-440`, `eq:criticalenergy`:
  `½(y²)' + (ν-C₀y)z² ≤ by` at every interior time.
  Exact quantifier order: `ν,hν,g,hg,T,w,t,ht`, followed by an actual
  derivative witness.
  Non-vacuity: existence of `E'` prevents an implication from a nonexistent
  derivative; `reductionRegular` makes every `toReal` operand finite. -/
  criticalEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ E' : ℝ,
            HasDerivAt
                (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2)
                E' t ∧
              E' / 2 +
                  (ν - C₀ *
                    (criticalY (meanFreeVelocity g w.velocity) t).toReal) *
                    (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 ≤
                (criticalB (meanFreeForce g) t).toReal *
                  (criticalY (meanFreeVelocity g w.velocity) t).toReal

  /-- `03-torus.tex:441-444`, `eq:bintegral`:
  `∫₀∞ b(t)dt ≤ ρ`.
  Exact quantifier order: `g,hg`; no viscosity or solution is needed.
  Non-vacuity: both sides are fail-safe `ℝ≥0∞` quantities based on
  integrable Fourier data paths, and `g∈forceClassT` is explicit. -/
  bIntegral : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    criticalBIntegral (meanFreeForce g) ≤ criticalRho g

  /-- `03-torus.tex:446-458`, `eq:ybound`, after the continuity bootstrap:
  `y(t) ≤ ∫₀ᵗ b(s)ds ≤ ρ` throughout the classical lifespan.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,t,ht`.
  Non-vacuity: the strict smallness hypothesis uses the positive finite
  threshold `cν`, and the conclusion bounds the concrete homogeneous norm. -/
  yBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ico (0 : ℝ) T,
            criticalY (meanFreeVelocity g w.velocity) t ≤
                ∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s ∧
              (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤
                criticalRho g

  /-- `03-torus.tex:467-484`, `eq:H1energy`:
  `(‖∇v‖²₂)' + ν‖Δv‖²₂ ≤ Cν⁻¹‖h‖²₂`.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,t,ht`, followed by an
  actual derivative witness.
  Non-vacuity: `reductionRegular` supplies finiteness for every norm passed
  to `toReal`, and existence of `E'` rules out a vacuous derivative premise. -/
  hOneEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            ∃ E' : ℝ,
              HasDerivAt
                  (fun s ↦ gradientSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (s, x))) E' t ∧
                E' + ν * laplacianSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ≤
                  CH1 * ν⁻¹ * lTwoSqT
                    (fun x ↦ meanFreeForce g (t, x))

  /-- `03-torus.tex:486-500`: orthogonal mode decomposition and the finite
  squared-`H²` bound used in `eq:criterion`:
  `∫₀ˢ‖u‖²_{H²} ≤ Sρ² + Cν⁻²∫₀∞‖h‖²₂ < ∞`.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,S,hS,hST`.
  Non-vacuity: the final conjunct explicitly proves the displayed upper bound
  finite; neither compact support nor a failed datum can be a junk zero. -/
  continuationBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ (S : ℝ), 0 < S → S ≤ T →
            squaredHTwoIntegralT S w.velocity =
                meanModeCriterionIntegral S g w.velocity ∧
              meanModeCriterionIntegral S g w.velocity ≤
                ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ∧
              ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤

  globalRegularity : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤

end NSFormalization.Section3.T20

/- copied verbatim from
formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:374. -/
namespace NSFormalization.Section3.T20

/-- Existential statement form of the copied T20 API; no inhabitant is
constructed in this specification lane. -/
def criticalRegularityStatement : Prop := Nonempty CriticalRegularityTAPI

end NSFormalization.Section3.T20

/-! **T21: main assembly on the torus.**

The preceding blocks are the canonical T19 and T20 carriers copied under the
namespaces prescribed by their source files.  This final namespace contains
only the two T21 result structures and the paper-order proposition aliases.
The force topology is represented by the registered `RelativelyDenseT`
predicate: its positive `ℝ≥0∞`-radius approximation clause is exactly the
relative closure characterization used in the manuscript. -/
namespace BlowupDensity.T21.DraftA

open Set Filter Topology
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.T19
open NSFormalization.Section3.T20
open scoped ENNReal Topology BigOperators

/-- The zero initial velocity occurring in `thm:main(ii)` and
`cor:nondensity` (`paper/sections/03-torus.tex:8-16,506-509`). -/
def zeroInitialVelocity : SpatialField := fun _ => 0

/-- The zero force, the centre of the relative critical ball
(`paper/sections/03-torus.tex:506-509`). -/
def zeroForce : SpaceTimeField := fun _ => 0

/-- `03-torus.tex:506-509`: the relative open ball in the force class, centred
at zero in the `L¹(0,∞;H^(1/2)(T³))` norm.  The radius is the critical theorem's
constant multiplied by the viscosity and is interpreted as an `ℝ≥0∞` radius,
because `criticalRho`/`forceSobolevENormT` are extended-valued norms.  The
strict inequality is the relative-ball condition; membership in `forceClassT`
is the ambient relative-space condition. -/
def criticalForceBall (critical : CriticalRegularityTAPI) (ν : ℝ) :
    Set SpaceTimeField :=
  {g | g ∈ forceClassT ∧
    criticalRho g < ENNReal.ofReal (critical.c * ν)}

/-! The copied critical-radius spelling is definitionally the registered
`L¹_t H^(1/2)` norm.  This is a drift check for the T20 copy against the
registered T11 norm used by the T21 ball. -/
example (g : SpaceTimeField) :
    criticalRho g = forceSobolevENormT 1 (1 / 2) g := rfl

/-! The registered breakdown set is the force-class specialization used by
the copied T19 density API. -/
example (ν : ℝ) (a : SpatialField) (T : ℝ) :
    breakdownSetT ν a T = breakdownSetInT forceClassT ν a T := rfl

/-- **`cor:nondensity`**, `paper/sections/03-torus.tex:506-509`.

The structure is parameterized by the copied T20 critical-regularity API, so
the `c` in every radius is exactly the constant selected by `prop:critical`;
no second or unrelated threshold constant is introduced.  It is `Prop`-valued:
the only datum exported by the paper is T20's already-parameterized `c`, while
each field below is a concrete conclusion about the registered force class,
norms, and lifespan. -/
structure NonDensityAPI (critical : CriticalRegularityTAPI) : Prop where
  /-- `03-torus.tex:506-509`: the critical ball has the paper's radius
  `cν`, and that radius is positive whenever `ν>0`.

  Exact quantifier order: `∀ ν`, then `0<ν`.

  Non-vacuity: this is strict positivity of the actual `ℝ≥0∞` radius
  `ENNReal.ofReal (critical.c*ν)`, not a declaration of an arbitrary ball. -/
  criticalRadius_pos :
    ∀ ν : ℝ, 0 < ν → 0 < ENNReal.ofReal (critical.c * ν)

  /-- `03-torus.tex:506-509`: zero is an element of the ambient force class,
  so the displayed critical ball is nonempty as a relative ball.

  Exact quantifier order: none.

  Non-vacuity: the membership is the registered smooth, periodic, compact
  positive-time support predicate, not an unconstrained inhabitant. -/
  zeroForce_mem_forceClass : zeroForce ∈ forceClassT

  /-- `03-torus.tex:506-509`: zero belongs to the relative critical ball for
  every positive viscosity.

  Exact quantifier order: `∀ ν`, then `0<ν`.

  Non-vacuity: the membership expands to force-class membership and the strict
  `L¹_tH^(1/2)` inequality at the stated radius `cν`. -/
  zero_mem_criticalBall :
    ∀ ν : ℝ, 0 < ν → zeroForce ∈ criticalForceBall critical ν

  /-- `03-torus.tex:506-509`: the small-critical-force ball misses the zero-data
  breakdown set `𝓑⁰_{ν,T}`.

  Exact quantifier order: `∀ ν`, `0<ν`, `∀ T`, `0<T`, then every force in the
  explicitly defined critical ball.

  Non-vacuity: the conclusion is genuine set disjointness: a ball member has
  a globally regular zero-data solution by T20, whereas membership in
  `breakdownSetT ν zeroInitialVelocity T` requires its maximal lifespan to be
  at most `ENNReal.ofReal T`. -/
  criticalBall_disjoint_zeroBreakdown :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ g : SpaceTimeField, g ∈ criticalForceBall critical ν →
        g ∉ breakdownSetT ν zeroInitialVelocity T

  /-- `03-torus.tex:507-509`: monotonicity of the force Sobolev norms in the
  order, `‖g‖_{L¹_tH^(1/2)} ≤ ‖g‖_{L¹_tH^s}` for `s≥1/2`.

  Exact quantifier order: `∀ s`, `1/2≤s`, `∀ g`, then `g∈𝓕`.

  Non-vacuity: both sides are the registered extended-valued Bochner norms and
  the force-class hypothesis supplies the paper's integrability/smoothness
  class; no `.toReal` or unguarded integral is used. -/
  sobolevMonotonicity :
    ∀ s : ℝ, (1 : ℝ) / 2 ≤ s →
      ∀ g : SpaceTimeField, g ∈ forceClassT →
        forceSobolevENormT 1 (1 / 2) g ≤ forceSobolevENormT 1 s g

  /-- `03-torus.tex:507-509`: non-density at and above the critical exponent,
  obtained from the ball and the monotonicity clause.

  Exact quantifier order: `∀ ν`, `0<ν`, `∀ T`, `0<T`, `∀ s`, `1/2≤s`.

  Non-vacuity: this is negation of the registered `RelativelyDenseT` relative
  closure predicate in the exact `L¹(0,∞;H^s)` topology, not merely a claim
  that one chosen approximating sequence fails. -/
  nonDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
      (1 : ℝ) / 2 ≤ s →
        ¬ RelativelyDenseT 1 s forceClassT
            (breakdownSetT ν zeroInitialVelocity T)

/-- **`thm:main` (i), `paper/sections/03-torus.tex:8-12`**.

For every fixed admissible initial velocity, the torus breakdown set is dense
below `1/2` in the relative `L¹(0,∞;H^s(T³))` topology. -/
structure MainTheoremAPI : Prop where
  /-- Clause (i), `03-torus.tex:8-12`: fixed-initial-data density.

  Exact quantifier order: `∀ a`, `a∈𝓧`, `∀ ν`, `0<ν`, `∀ T`, `0<T`,
  `∀ s`, `s<1/2`, then the relative-density conclusion.

  Non-vacuity: `RelativelyDenseT` quantifies over every force in `𝓕` and every
  positive `ℝ≥0∞` radius and produces an actual member of
  `breakdownSetT ν a T` at strictly smaller registered `L¹_tH^s` distance. -/
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < (1 : ℝ) / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

  /-- Clause (ii), forward direction, `03-torus.tex:10-16`: at zero initial
  velocity, every subcritical order has dense breakdown forces.

  Exact quantifier order: `∀ ν`, `0<ν`, `∀ T`, `0<T`, `∀ s`, `s<1/2`.

  Non-vacuity: the conclusion is the same positive-radius relative closure
  predicate as clause (i), now specialized to `zeroInitialVelocity`. -/
  zeroInitialDensity_subcritical :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
      s < (1 : ℝ) / 2 →
        RelativelyDenseT 1 s forceClassT
          (breakdownSetT ν zeroInitialVelocity T)

  /-- Clause (ii), reverse direction, `03-torus.tex:10-16`: at zero initial
  velocity, density forces the order to be strictly below `1/2`.

  Exact quantifier order: `∀ ν`, `0<ν`, `∀ T`, `0<T`, `∀ s`, followed by the
  relative-density hypothesis and the strict subcritical conclusion.

  Non-vacuity: the antecedent is the full registered density predicate, so this
  field explicitly rules out density at equality and above rather than relying
  on an unguarded numerical assertion. -/
  zeroInitialDensity_only_if :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
      RelativelyDenseT 1 s forceClassT
          (breakdownSetT ν zeroInitialVelocity T) →
        s < (1 : ℝ) / 2

/-- The complete theorem statement in the paper's order,
`03-torus.tex:8-16`: clause (i) followed by the biconditional in clause (ii).
The biconditional is written here even though `MainTheoremAPI` stores its two
directions as separate fields, so both directions remain individually usable. -/
def mainStatement : Prop :=
  (∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < (1 : ℝ) / 2 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)) ∧
  (∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT
        (breakdownSetT ν zeroInitialVelocity T) ↔
      s < (1 : ℝ) / 2)

/-- The corollary statement in the paper's order,
`03-torus.tex:506-509`: the zero-data breakdown set is not dense at every
order at or above the critical exponent. -/
def nonDensityStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    (1 : ℝ) / 2 ≤ s →
      ¬ RelativelyDenseT 1 s forceClassT
        (breakdownSetT ν zeroInitialVelocity T)

/-- Assembly signature for `thm:main`: the T19 density package, the T20
critical-regularity package, and the assembled T21 non-density package are the
three inputs consumed by the final theorem.  This is intentionally a `Prop`
signature rather than an unproved inhabitant of the arrow type. -/
def mainOfInputs : Prop :=
  ∀ (_density : PeriodicDensityAPI)
    (_critical : CriticalRegularityTAPI),
      NonDensityAPI _critical → MainTheoremAPI

end BlowupDensity.T21.DraftA
