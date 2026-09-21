import Contracts.V1.Data
import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.MainThresholds
import Contracts.V1.CompletedDensity
import Contracts.V1.Packet
import Contracts.V1.PacketImport
import Contracts.V1.MaximalPartial
import Contracts.V1.Correction
import Contracts.V1.GradientL6

/-!
# T21 blind draft B: the main assembly on `T³`
# (`cor:nondensity` and `thm:main` (i)+(ii))

Statement-only specification of the two top-level results of Section 3,
`paper/sections/03-torus.tex`:

* `NonDensityAPI`  — `cor:nondensity`, non-density at and above the critical
  exponent (`:506-509`, proof `:510-520`);
* `MainTheoremAPI` — `thm:main`, the Sobolev density threshold, clauses (i) and
  (ii) (`:6-16`, proof `:522-524`, scope remark `:525`).

There are no proofs in this file.  It elaborates with `0` errors under
`cd verification && lake env lean ../research/T21/DraftB.lean`.

## Copy policy (`CLAUDE.md` contract rules, T13 copy policy)

Everything **registered** is imported and used by name, never restated:
`ClassicalSolutionT`, `maximalLifespanT`, `RegularThroughT`, `breakdownSetT`,
`breakdownSetInT`, `RelativelyDenseT`, `forceClassT`, `initialClassT`,
`forceSobolevENormT`, `energyENormT`, `energyEssSupT`, `squaredHTwoIntegralT`,
`galileanMeanT`, `forceMeanT`, `periodicSobolevENorm`,
`periodicHomogeneousENorm`, `IsMeanZeroT`, `criticalOrder`, `alpha`,
`MaximalPartial.{limsupLeft,speedENorm}` (`Contracts/V1/TorusData.lean`,
`Contracts/V1/TorusLocalTheory.lean`, `Contracts/V1/Data.lean`,
`Contracts/V1/Correction.lean`, `Contracts/V1/MaximalPartial.lean`).

Everything **unregistered that this node consumes** is copied verbatim, in
delimited blocks carrying their source lines and keeping their source
namespaces:

* `BlowupDensity.T15.Draft` + `BlowupDensity.T19` — the four reconciled T19
  structures (`PeriodicDensityAPI`, `MixedRegionAPI`, `StrongClosureAPI`,
  `ProjectionAPI`) and their local objects, copied from
  `research/T19/Spec.lean:91-529`.  Only `PeriodicDensityAPI` is consumed by
  `thm:main`; the other three are the `03-torus.tex:527-590` corollaries of
  `prop:density`, copied unchanged so that no field of this file re-invents
  them.
* `BlowupDensity.T12.Draft` — the T12 membership/derivative vocabulary needed
  to state the T20 record, copied from `research/T20/Spec.lean:611-699`.
* `BlowupDensity.T20.Spec` — the reconciled `CriticalRegularityTAPI` of
  `prop:critical` with its constants and the `criticalRho` ball vocabulary,
  copied from `research/T20/Spec.lean:894-1245`.  It is textually identical to
  the canonical `NSFormalization.Section3.T20.CriticalRegularityTAPI`
  (`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:139`).

**One deliberate re-basing of the copies.**  `research/T20/Spec.lean` predates
the registration of `Contracts/V1/TorusLocalTheory.lean` and therefore opened
its own `BlowupDensity.T10.Draft` / `BlowupDensity.T11.Draft` restatements of
`ClassicalSolutionT`, `maximalLifespanT`, `forceClassT`, `forceSobolevENormT`,
`squaredHTwoIntegralT`, `galileanMeanT` and `forceMeanT`.  Those two `open`
lines are replaced here by `open BlowupDensity.Contracts.V1.TorusLocalTheory`,
so the copied text is unchanged while every such name resolves to the
**registered** contract — the same choice `research/T19/Spec.lean` makes.  For
the `def`s this is invisible (`forceSobolevENormT` and `forceClassT` are
definitionally the canonical ones, checked below and against
`NSFormalization.Section3.T10` in `research/T21/COMPARISON_B.md`); for
`ClassicalSolutionT` it is the `CLAUDE.md` **structure exception**, so
`maximalLifespanT` is the registered one throughout this file and
`Bindings.TorusLocalTheory` is what converts it to the canonical record.

## Type vs `Prop`

* `BlowupDensity.T20.Spec.CriticalRegularityTAPI` stays **`Type`-valued** (as
  copied): `prop:critical` selects the smallness constant `c` and three
  absolute estimate constants before every `ν`, `g`, `T`.
* `NonDensityAPI c` is **`Prop`-valued**, indexed by the real parameter `c`:
  `cor:nondensity` (`:506-508`) introduces no constant of its own, and the one
  constant its proof uses is `prop:critical`'s.  The index is pinned to a
  genuine `prop:critical` constant by the fields `hc` and
  `criticalGlobalRegularity`, which are exactly `CriticalRegularityTAPI.hc`
  and `CriticalRegularityTAPI.globalRegularity`; without them a nonsensical
  `c` would make the ball clauses meaningless.
* `MainTheoremAPI` is **`Prop`-valued**: `thm:main` (`:6-16`) exports neither a
  constant nor a datum; its only number, the threshold `1/2`, is a literal and
  is pinned to the registered `criticalOrder 1`.  This follows the T19/T24
  data-free `Prop` precedent and diverges from the `Type`-valued registry
  convention of `MainThresholdsAPI` / `CompletedDensityAPI` (owner question,
  recorded in `research/T21/COMPARISON_B.md`).

## What differs from the Section 4 counterpart

`Contracts/V1/MainThresholds.lean` (`R41`, `04-whole-space.tex:7-15`
`thm:Rmain`) is the same two-clause theorem with three differences, each
recorded field by field in `research/T21/COMPARISON_B.md`:

1. a **single** critical exponent `1/2` and **`q = 1` only** — the torus has a
   spectral gap, so `04-whole-space.tex`'s `q ∈ {1,2}` and
   `s_q = 2/q - 3/2` collapse to `criticalOrder 1 = 1/2`
   (`collaboration/SECTION3_PLAN.md` §4);
2. `thm:main` carries **no regular-reference rider**: the whole-space
   `MainThresholdsAPI.regularReferenceApproximation` clause
   (`04-whole-space.tex:13`) lives on the torus in `cor:closure`, i.e. in
   `BlowupDensity.T19.StrongClosureAPI`, not here;
3. the non-density half is proved through an **explicit ball of radius `cν`**
   in `L¹_tH^{1/2}` (`:511-519`); `R41` states only the biconditional and
   leaves the ball inside its own converse.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal Topology BigOperators

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
/- copied verbatim from research/T12/Spec.lean:166-172,189-257,270-470
(selected declarations; registered definitional-check examples are unused). -/
namespace BlowupDensity.T12.Draft

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

end BlowupDensity.T12.Draft
/- end verbatim T12 copy -/

/- copied verbatim from `research/T20/Spec.lean:894-1245`, itself the
reconciled T20 node; textually identical to the canonical
`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:30-386`.
The two `open BlowupDensity.T1{0,1}.Draft` lines of the source are replaced by
`open BlowupDensity.Contracts.V1.TorusLocalTheory` (see the module docstring);
no declaration text is changed. -/
namespace BlowupDensity.T20.Spec

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.T12.Draft
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


end BlowupDensity.T20.Spec
/- end verbatim T20 copy -/

/-! # T21: the node's own declarations

Nothing below is copied: these are the renderings of `cor:nondensity` and
`thm:main` themselves.  Every norm is `ℝ≥0∞`-valued (`forceSobolevENormT`,
`periodicSobolevENorm`), so a missing representative reports `⊤` rather than a
junk zero; every viscosity and horizon carries `0 < ν`, `0 < T`; and no real
supremum or `.toReal` occurs. -/

namespace BlowupDensity.T21.DraftB

open BlowupDensity.T20.Spec (criticalRho CriticalRegularityTAPI)

/-! ## 0. The two sets named in the statements -/

/-- `02-preliminaries.tex:41` `eq:singularforces` and `03-torus.tex:10,12`:
`𝓑⁰_{ν,T} = 𝓑_{ν,0,T}`, the forces producing classical breakdown by `T` from
the zero initial velocity.  This is the exact torus mirror of the registered
whole-space `Data.breakdownSetRZero`; the `example` below checks that the
registered definition has this same shape.  The zero datum is spelled
`fun _ : Space ↦ 0`, the same literal used by
`BlowupDensity.T20.Spec.CriticalRegularityTAPI.globalRegularity`. -/
def breakdownSetTZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetT ν (fun _ : Space ↦ 0) T

/-- `03-torus.tex:511-514` and `:519`: the open ball of the corollary's proof,
`{g ∈ 𝓕 : ‖g‖_{L¹_tH^s_x} < cν}`.  At `s = 1/2` this is the display `:513`
whose radius is the `prop:critical` constant times the viscosity; at a general
`s ≥ 1/2` it is the ball of `:519`.  The radius is `ENNReal.ofReal (c * ν)`,
matching `CriticalRegularityTAPI`'s own smallness hypothesis, and the
membership `g ∈ forceClassT` keeps the ball *relative* to `𝓕` as the paper
requires. -/
def criticalBallT (c ν s : ℝ) : Set SpaceTimeField :=
  {g | g ∈ forceClassT ∧ forceSobolevENormT 1 s g < ENNReal.ofReal (c * ν)}

/-! ### Definitional checks against registered and copied spellings -/

/-- `breakdownSetTZero` has the shape of the registered whole-space
`Data.breakdownSetRZero` (`Contracts/V1/Data.lean:686`). -/
example (ν T : ℝ) :
    BlowupDensity.Contracts.V1.Data.breakdownSetRZero ν T =
      BlowupDensity.Contracts.V1.Data.breakdownSetR ν (fun _ : Space ↦ 0) T :=
  rfl

/-- At `s = 1/2` the ball is exactly the `prop:critical` smallness region:
its norm is the copied `BlowupDensity.T20.Spec.criticalRho`. -/
example (c ν : ℝ) (g : SpaceTimeField) :
    g ∈ criticalBallT c ν (1 / 2) ↔
      (g ∈ forceClassT ∧ criticalRho g < ENNReal.ofReal (c * ν)) :=
  Iff.rfl

/-- `criticalRho` is the registered `L¹(0,∞;H^{1/2}(T³))` norm, not a copy of
it (`Contracts/V1/TorusLocalTheory.lean:89`). -/
example (g : SpaceTimeField) :
    criticalRho g = forceSobolevENormT 1 (1 / 2) g := rfl

/-- The copied T12 derivative vocabulary is token-for-token the registered
`Contracts/V1/GradientL6.lean:78,89-90,94-95` (namespace
`BlowupDensity.Contracts.V1`). -/
example : BlowupDensity.T12.Draft.lift =
    BlowupDensity.Contracts.V1.lift := rfl

example : BlowupDensity.T12.Draft.gradientTensor =
    BlowupDensity.Contracts.V1.gradientTensor := rfl

example : BlowupDensity.T12.Draft.laplacian =
    BlowupDensity.Contracts.V1.laplacian := rfl

/-- The relative topology of `03-torus.tex:7` and `:508`, unfolded: density in
`𝓕` for the `L¹(0,∞;H^s(T³))` pseudometric is approximation of every reference
force at every positive `ℝ≥0∞` radius. -/
example (ν T s : ℝ) :
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) =
      (∀ g ∈ forceClassT, ∀ r : ℝ≥0∞, 0 < r →
        ∃ f ∈ breakdownSetTZero ν T, forceSobolevENormT 1 s (f - g) < r) :=
  rfl

/-! ## 1. `cor:nondensity` (`03-torus.tex:506-509`, proof `:510-520`)

**`Prop`-valued, indexed by the real `c`.**  The corollary states no constant
of its own; the only constant in its proof is `prop:critical`'s, so it enters
as the index and is pinned to a genuine `prop:critical` constant by the fields
`hc` and `criticalGlobalRegularity` — which are verbatim
`CriticalRegularityTAPI.hc` and `CriticalRegularityTAPI.globalRegularity`.
Without that pin the remaining fields would speak about an arbitrary ball. -/

/-- **`cor:nondensity` — non-density at and above the critical exponent,
`paper/sections/03-torus.tex:506-509`, proof `:510-520`.**

For every `s ≥ 1/2` and `T > 0`, `𝓑⁰_{ν,T}` is not dense in `𝓕` for the
relative `L¹_tH^s_x` topology.  The proof exhibits the ball
`{g ∈ 𝓕 : ‖g‖_{L¹_tH^s_x} < cν}`: nonempty, relatively open, containing zero,
and — by `prop:critical` together with the Fourier-weight monotonicity of the
`H^s` norms — disjoint from the singular-force set.

`c` is the `prop:critical` constant (`:384`); `NonDensityAPI K.c` is the
intended instantiation for `K : CriticalRegularityTAPI`. -/
structure NonDensityAPI (c : ℝ) : Prop where
  /-- `03-torus.tex:384`: positivity of the `prop:critical` smallness
  constant.

  Exact quantifier order: none; `c` is the structure index.

  Non-vacuity: with `0 < ν` this makes `ENNReal.ofReal (c * ν)` a strictly
  positive radius, so `criticalBallT c ν s` is a genuine ball and not the
  empty set that would make every disjointness clause below vacuous. -/
  hc : 0 < c

  /-- `03-torus.tex:383-389` `prop:critical`, the imported input: a force in
  `𝓕` with `ρ = ‖g‖_{L¹(0,∞;H^{1/2})} < cν` has infinite maximal lifespan from
  rest.  This field is `CriticalRegularityTAPI.globalRegularity` verbatim, with
  `maximalLifespanT` the registered one.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ g, g ∈ 𝓕 → ρ(g) < ofReal (c*ν) →`
  `maximalLifespanT ν 0 g = ⊤`.

  Non-vacuity: it pins the index `c` to a constant for which `prop:critical`
  actually holds; the conclusion is the registered `ℝ≥0∞` lifespan being `⊤`,
  which is what makes the ball disjoint from every `𝓑⁰_{ν,T}`. -/
  criticalGlobalRegularity : ∀ ν : ℝ, 0 < ν →
    ∀ g : SpaceTimeField, g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤

  /-- `03-torus.tex:515` "is a nonempty relative open ball, containing zero":
  the zero force lies in the ball, at every order `s`.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ s : ℝ,`
  `(0 : SpaceTimeField) ∈ criticalBallT c ν s`.

  Non-vacuity: this is two genuine assertions at once — `0 ∈ 𝓕` (the zero
  force really is an admissible smooth compactly-time-supported force) and
  `forceSobolevENormT 1 s 0 < ofReal (c*ν)`, i.e. the registered `⨅`-norm of
  the zero field is *attained*, not `⊤`.  It also supplies the nonemptiness
  the last sentence of `:519` needs. -/
  zeroMemBall : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    (0 : SpaceTimeField) ∈ criticalBallT c ν s

  /-- `03-torus.tex:515` "relative open ball": openness of the ball in the
  relative `L¹_tH^s_x` pseudometric on `𝓕`, stated in the `ε`-form that
  `RelativelyDenseT` also uses (there is no `TopologicalSpace` instance on the
  force class).

  Exact quantifier order: `∀ ν, 0 < ν → ∀ s, ∀ g ∈ criticalBallT c ν s,`
  `∃ r : ℝ≥0∞, 0 < r ∧ ∀ f ∈ 𝓕, ‖f-g‖_{L¹_tH^s} < r → f ∈ criticalBallT c ν s`.

  Non-vacuity: the radius `r` is quantified inside the ball point, so the
  statement is the honest "every point is interior"; discharging it needs the
  triangle inequality for the registered `⨅`-norm (it is not implied by the
  definition of `criticalBallT`). -/
  ballRelativelyOpen : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    ∀ g ∈ criticalBallT c ν s,
      ∃ r : ℝ≥0∞, 0 < r ∧
        ∀ f ∈ forceClassT, forceSobolevENormT 1 s (f - g) < r →
          f ∈ criticalBallT c ν s

  /-- `03-torus.tex:517` "the Fourier weights imply", at the level of the
  registered coefficient data: transporting a datum from order `t` down to
  order `s ≤ t` by the registered `IsPeriodicReweight` does not increase its
  norm, because the weight `(1+4π²|k|²)^{(s-t)/2}` is at most one.

  Exact quantifier order: `∀ s t : ℝ, s ≤ t → ∀ A : PeriodicSobolev t,`
  `∀ B : PeriodicSobolev s, IsPeriodicReweight t s A B → ‖B‖ ≤ ‖A‖`.

  Non-vacuity: `IsPeriodicReweight` is the registered coefficient graph
  (`Contracts/V1/TorusData.lean:IsPeriodicReweight`), and the conclusion is an
  inequality of actual `ℓ²` norms in the complete real carrier — this is the
  mechanism sentence, not a restatement of the physical inequality below. -/
  reweightContraction : ∀ s t : ℝ, s ≤ t →
    ∀ (A : PeriodicSobolev t) (B : PeriodicSobolev s),
      IsPeriodicReweight t s A B → ‖B‖ ≤ ‖A‖

  /-- `03-torus.tex:517-518`: `‖g(t)‖_{H^{1/2}} ≤ ‖g(t)‖_{H^s}` for `s ≥ 1/2`,
  on a single time slice.

  Exact quantifier order: `∀ s : ℝ, 1/2 ≤ s → ∀ z : SpatialField,`
  `periodicSobolevENorm (1/2) z ≤ periodicSobolevENorm s z`.

  Non-vacuity: no class hypothesis on `z` is needed and none is silently
  helping — both sides are the registered `⨅` over representing data, which is
  `⊤` when no datum exists, so the inequality is the real comparison of two
  extended norms rather than a comparison of junk zeros. -/
  sliceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ z : SpatialField,
    periodicSobolevENorm (1 / 2) z ≤ periodicSobolevENorm s z

  /-- `03-torus.tex:517-519`: the time-integrated form actually used,
  `‖g‖_{L¹_tH^{1/2}_x} ≤ ‖g‖_{L¹_tH^s_x}` for `s ≥ 1/2`; it is what makes the
  `L¹_tH^s_x` ball of radius `cν` a subset of the `L¹_tH^{1/2}_x` ball.

  Exact quantifier order: `∀ s : ℝ, 1/2 ≤ s → ∀ f : SpaceTimeField,`
  `forceSobolevENormT 1 (1/2) f ≤ forceSobolevENormT 1 s f`.

  Non-vacuity: this is a strictly stronger statement than the slice clause —
  the two sides are infima over *strongly measurable representing paths*, so
  discharging it requires transporting a whole path, not just one datum. -/
  forceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ f : SpaceTimeField,
    forceSobolevENormT 1 (1 / 2) f ≤ forceSobolevENormT 1 s f

  /-- `03-torus.tex:511-516`: at `s = 1/2` the ball is disjoint from
  `𝓑⁰_{ν,T}`, by `prop:critical`.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T →`
  `Disjoint (criticalBallT c ν (1/2)) (breakdownSetTZero ν T)`.

  Non-vacuity: `Disjoint` is on honest inhabited sets — `zeroMemBall` shows the
  first is nonempty — and the second is the registered breakdown set, so this
  is the actual separation the corollary needs, not disjointness from `∅`. -/
  criticalBallDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    Disjoint (criticalBallT c ν (1 / 2)) (breakdownSetTZero ν T)

  /-- `03-torus.tex:519` first sentence: for every `s ≥ 1/2` the ball
  `‖g‖_{L¹_tH^s_x} < cν` is also disjoint from the singular-force set — the
  previous field combined with `forceSobolevMonotone`.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ s, 1/2 ≤ s →`
  `Disjoint (criticalBallT c ν s) (breakdownSetTZero ν T)`.

  Non-vacuity: the order `s` ranges over the whole critical-and-above half
  line, and the ball keeps the same radius `cν` as at `s = 1/2`; nothing here
  degenerates as `s` grows because the ball only shrinks. -/
  ballDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
    Disjoint (criticalBallT c ν s) (breakdownSetTZero ν T)

  /-- `03-torus.tex:507-508`, the corollary itself, with `:519` last sentence
  ("a dense subset cannot miss a nonempty open set") as its proof: for every
  `s ≥ 1/2` and `T > 0`, `𝓑⁰_{ν,T}` is **not** dense in `𝓕` for the relative
  `L¹_tH^s_x` topology.

  Exact quantifier order, following `:507`: `∀ ν, 0 < ν → ∀ s, 1/2 ≤ s →`
  `∀ T, 0 < T → ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)`.

  Non-vacuity: the negated predicate is the registered positive-radius density
  notion whose distance is the fail-safe `ℝ≥0∞` norm; refuting it means
  producing one reference force and one radius that no breakdown force meets,
  which is precisely the ball above. -/
  nonDensity : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

/-- **`cor:nondensity` in the paper's quantifier order, `03-torus.tex:507-508`.**
Equals the field `NonDensityAPI.nonDensity` and is independent of `c`. -/
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

/-! ## 2. `thm:main` (`03-torus.tex:6-16`, proof `:522-524`)

**`Prop`-valued.**  The theorem exports neither a constant nor a datum: its
only number is the literal threshold `1/2`, pinned below to the registered
`criticalOrder 1`.  This follows the data-free `Prop` choice of
`research/T19/Spec.lean` and diverges from the `Type`-valued registry
convention of `Contracts/V1/MainThresholds.lean` (owner question, recorded in
`research/T21/COMPARISON_B.md`). -/

/-- **`thm:main` — Sobolev density threshold,
`paper/sections/03-torus.tex:6-16`, proof `:522-524`, scope remark `:525`.**

Equip `𝓕` with its relative `L¹(0,∞;H^s(T³))` norm topology (`:7`; on the
torus the exponent is `q = 1` only, `collaboration/SECTION3_PLAN.md` §4).
Then (i) for every fixed `a ∈ 𝓧` the set `𝓑_{ν,a,T}` is dense if `s < 1/2`,
and (ii) for zero initial velocity `𝓑⁰_{ν,T}` is dense **iff** `s < 1/2`.

The proof `:523` names its two inputs: `prop:density` (= T19
`PeriodicDensityAPI.fixedInitialDensity`) for the density half and
`cor:nondensity` (= `NonDensityAPI.nonDensity`) for the non-density half. -/
structure MainTheoremAPI : Prop where
  /-- `03-torus.tex:9,13`: the torus threshold `1/2` is the registered
  Section 4 threshold function at `q = 1`, `criticalOrder 1 = 2/1 - 3/2`.
  The paper writes `1/2` literally, so every density field below writes it
  literally too; this field is what ties the two spellings together and
  reproduces `MainThresholdsAPI.thresholdValues`' first conjunct.

  Exact quantifier order: none.

  Non-vacuity: a concrete equality of reals between the registered threshold
  function and the literal used in the statements, not an opaque proposition.
  On the torus this is the *only* threshold: `q = 2` has no torus counterpart
  (`SECTION3_PLAN.md` §4), so there is no second conjunct. -/
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2

  /-- `03-torus.tex:10` "for zero initial velocity" together with
  `02-preliminaries.tex:9` `eq:inputspaces`: the zero field is an admissible
  initial velocity, i.e. `0 ∈ 𝓧 = C^∞_div(T³;R³)`.

  Exact quantifier order: none.

  Non-vacuity: this is what makes clause (ii) an instance of clause (i) rather
  than a statement about a datum outside the class; it unfolds to smoothness,
  unit periodicity and solenoidality of `fun _ : Space ↦ 0`. -/
  zeroInitialClass : (fun _ : Space ↦ 0) ∈ initialClassT

  /-- **Clause (i)**, `03-torus.tex:9`: for every fixed `a ∈ 𝓧`, the set
  `𝓑_{ν,a,T}` is dense in `𝓕` for the relative `L¹_tH^s_x` topology whenever
  `s < 1/2`.  This is `prop:density` (`:349-356`) read as an assertion of the
  theorem; it equals `BlowupDensity.T19.PeriodicDensityAPI.fixedInitialDensity`
  up to the position of the `ν`, `T` binders.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ a, a ∈ 𝓧 → ∀ s,`
  `s < 1/2 → RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)`.

  Non-vacuity: the conclusion is the registered positive-radius density
  predicate over the registered breakdown set — the witness must be an actual
  force of `𝓕` whose registered maximal lifespan is at most `T`. -/
  fixedInitialDensity : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ s : ℝ, s < 1 / 2 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

  /-- **Clause (ii)**, `03-torus.tex:10-14`: for zero initial velocity,
  `𝓑⁰_{ν,T}` is dense in `𝓕` **if and only if** `s < 1/2`.  Both directions
  are kept under exactly the same hypotheses in a single biconditional, the
  shape of the registered whole-space
  `MainThresholdsAPI.zeroInitialDensityIff`; equality of orders (`s = 1/2`) is
  included on the non-density side.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ s : ℝ,`
  `RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1/2`.

  Non-vacuity: the left side is the registered density predicate specialized to
  the concrete zero-datum breakdown set, so neither direction can be discharged
  by an unconstrained proposition; the right side is a strict inequality of
  reals, not a placeholder. -/
  zeroInitialDensityIff : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2

  /-- `03-torus.tex:523`: the second of "the two assertions of the theorem" in
  the polarity in which `cor:nondensity` supplies it — non-density for zero
  initial velocity at every `s ≥ 1/2`.  Logically it is the contrapositive of
  the forward direction of `zeroInitialDensityIff`; it is kept as its own field
  because `:523` names it as an assertion of the theorem and because it is the
  clause a consumer inherits from `NonDensityAPI.nonDensity` (the registered
  `MainThresholdsAPI` keeps only the biconditional).

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ s, 1/2 ≤ s →`
  `¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)`.

  Non-vacuity: the negation is of the registered density predicate; it is
  refuted by an explicit reference force and radius, and `1/2 ≤ s` includes the
  critical order itself. -/
  zeroInitialNonDensity : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, 1 / 2 ≤ s →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

/-- **`thm:main` in the paper's quantifier order, `03-torus.tex:6-16`.**
Clause (i) followed by clause (ii), under the fixed `ν, T > 0` of
`02-preliminaries.tex:38`.  Equals the conjunction of
`MainTheoremAPI.fixedInitialDensity` and
`MainTheoremAPI.zeroInitialDensityIff`. -/
def mainStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    (∀ a : SpatialField, a ∈ initialClassT →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)) ∧
      ∀ s : ℝ,
        RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2

/-! ## 3. What the assembly consumes

`03-torus.tex:523` is the whole proof of `thm:main`, and `:516` is the whole
proof of the disjointness in `cor:nondensity`.  The three signatures below
record that dependency as arrow types; no inhabitant is constructed here. -/

/-- `03-torus.tex:511-516`: `cor:nondensity` is derived from `prop:critical`
alone — its constant `c`, its positivity, and its global-regularity
conclusion.  No part of the construction spine (`thm:packet`,
`thm:insertion`, T19's `prop:density`) is used, exactly as `:380-381` says. -/
def nonDensityOfCritical : Prop :=
  ∀ K : CriticalRegularityTAPI, NonDensityAPI K.c

/-- `03-torus.tex:523`: `thm:main` is `prop:density` plus `cor:nondensity` and
nothing else.  The `c` is bound universally because the theorem does not
mention it. -/
def mainOfDensityAndNonDensity : Prop :=
  ∀ c : ℝ,
    BlowupDensity.T19.PeriodicDensityAPI → NonDensityAPI c → MainTheoremAPI

/-- The two-input form asked for by the node: T19's density package and T20's
critical-regularity package assemble `thm:main`, through
`nonDensityOfCritical`.  T19's other three structures (`MixedRegionAPI`,
`StrongClosureAPI`, `ProjectionAPI`) are corollaries of `prop:density` at
`03-torus.tex:527-590` and are **not** consumed here; neither are the packet
and insertion contracts, which T19 has already absorbed. -/
def mainOfInputs : Prop :=
  BlowupDensity.T19.PeriodicDensityAPI →
    CriticalRegularityTAPI →
      MainTheoremAPI

end BlowupDensity.T21.DraftB
