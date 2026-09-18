import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.CompletedDensity
import Contracts.V1.MainThresholds

/-!
# T19 draft B: the periodic density package on `T³`
(`prop:density`, `cor:mixed`, `cor:closure`, `prop:projection`)

Statement-only draft B (double-blind, lane 372) of the four Section 3 density
results, `paper/sections/03-torus.tex:349-631`:

* `prop:density` (`:349-361`): density for each fixed initial velocity in the
  `L¹(0,∞;H^s(T³))` topology for `s < 1/2`;
* `cor:mixed` (`:528-539`): the sufficient mixed-Lebesgue region `3/p+2/q>3`;
* `cor:closure` (`:540-563`): strong closure in energy and dissipation, with
  simultaneous `E_T × L¹_tH^s` convergence;
* `prop:projection` (`:564-631`): projection of extended singular data, with the
  `∀a∃f` quantifier order and the `a=0 ↦ {0}` fiber.

One structure per result: `PeriodicDensityAPI`, `MixedRegionAPI`,
`StrongClosureAPI`, `ProjectionAPI`.  Each field is one clause of the paper's
statement, cited by line, with the exact quantifier order and a non-vacuity
note.  All four structures are `Prop`-valued: none of the four results
introduces constants or data (every conclusion is a proposition, with the
constructed families and forces bound existentially inside a field), so the
`Type`-valued container is unnecessary here.  This differs from the registered
Section 4 twins `MainThresholdsAPI` / `CompletedDensityAPI`
(`Contracts/V1/MainThresholds.lean`, `Contracts/V1/CompletedDensity.lean`),
which are declared as `Type` by registry convention although their fields are
also all `Prop`s.

## Vocabulary

Registered, imported and used by name (never copied):
`RelativelyDenseT`, `breakdownSetT`, `forceClassT`, `initialClassT`,
`maximalLifespanT`, `RegularThroughT`, `ClassicalSolutionT`, `energyENormT`,
`forceSobolevENormT` (`Contracts/V1/TorusLocalTheory.lean`); `criticalOrder`
(`Contracts/V1/Data.lean`); `BlowupDensity.Contracts.V1.alpha`
(`Contracts/V1/Correction.lean`).  The Section 4 counterparts
`MainThresholdsAPI`, `CompletedDensityAPI`, `RelativelyDense`, `breakdownSetIn`
are imported for the field-for-field comparison recorded in
`research/T19/COMPARISON_B.md`.

Unregistered, copied verbatim (T13 copy policy): the mixed-Lebesgue torus norm
`mixedLebesgueENormT`, its slice-path predicate `IsPeriodicLebesgueSlicePath`,
and the scaling exponent `alphaT`, copied from `research/T18/Spec.lean:395-442`
(themselves the T15 vocabulary) in their historical namespace
`BlowupDensity.T15.Draft`, with an `example … := rfl` drift check against the
registered `BlowupDensity.Contracts.V1.alpha`.

No T20 (`prop:critical`) vocabulary is imported: the density package is
entirely constructive (its proofs consume `thm:insertion` = T18), and does not
consume `prop:critical`, which belongs to the non-density spine T20/T21.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal Topology BigOperators

/- copied verbatim from research/T18/Spec.lean:395-442
   (the `BlowupDensity.T15.Draft` mixed-Lebesgue torus vocabulary, itself the
   T15 layer); dependencies resolve through the registered
   `Contracts.V1.TorusData` / `Contracts.V1.Data`. -/
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

/-- `03-torus.tex:130-131`: `α(p,q)=-3+3/p+2/q`, with
`ENNReal.toReal ⊤=0`. -/
def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

end BlowupDensity.T15.Draft
/- end verbatim T15/T18 copy -/

/-- Drift check `03-torus.tex:130-131`: the copied `alphaT` is definitionally the
registered `Contracts.V1.alpha` in which `cor:mixed`'s region and rate are
written; `check rfl`. -/
example (p q : ℝ≥0∞) :
    BlowupDensity.T15.Draft.alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

namespace BlowupDensity.T19.DraftB

open BlowupDensity.T15.Draft

/-! ## Mixed-Lebesgue relative density

`cor:mixed` states density in the `L^q(0,∞;L^p(T³))` topology, which the
registered `RelativelyDenseT` does not cover (it is the `H^s` Sobolev topology).
This predicate is the exact mixed-norm analogue of `RelativelyDenseT`,
`Contracts/V1/TorusLocalTheory.lean:227-231`, built from the registered
`breakdownSetT`/`forceClassT` and the copied honest torus mixed norm
`mixedLebesgueENormT`.  It is not a stub for any imported record; it is the
mixed-topology density predicate the corollary needs. -/
def RelativelyDenseMixedT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Y S : Set SpaceTimeField) : Prop :=
  ∀ g ∈ Y, ∀ r : ℝ≥0∞, 0 < r →
    ∃ f ∈ S, BlowupDensity.T15.Draft.mixedLebesgueENormT q p (fun z => f z - g z) < r

/-! ## 1. `prop:density`, `03-torus.tex:349-361` -/

/-- **Proposition `prop:density` (density for each fixed initial velocity),
`paper/sections/03-torus.tex:349-361`, with the closing distinction of
`:620-631`.**

`Prop`-valued: the proposition introduces no constant or datum; the approximant
`f` is bound existentially inside `RelativelyDenseT`.  Each field is one clause
of the proposition (and of the two-case proof).  The proof consumes T18
`thm:insertion` (`PeriodicInsertionAPI.lifespan`,
`.forceDifference_sobolev_bound`, `.forceDifference_negativeSobolev_tendsto`) in
the regular-reference case and nothing in the already-singular case; the
threshold `1/2` is the registered `criticalOrder 1`. -/
structure PeriodicDensityAPI : Prop where
  /-- `03-torus.tex:350-357`: for every fixed smooth divergence-free initial
  velocity `a`, positive viscosity `ν`, positive horizon `T`, and Sobolev order
  `s < 1/2`, the smooth compact torus forces whose maximal lifespan is at most
  `T` are relatively dense in the torus force class `𝓕` for the
  `L¹(0,∞;H^s(T³))` pseudometric.

  Exact quantifier order: `∀ a, a ∈ initialClassT → ∀ ν, 0 < ν → ∀ T, 0 < T →
  ∀ s, s < 1/2 → RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)`; the
  last conjunct unfolds to `∀ g ∈ 𝓕, ∀ r > 0, ∃ f ∈ 𝓑_{ν,a,T},
  ‖f - g‖_{L¹_tH^s} < r`, exactly the paper's `∀g∀ρ∃f`.

  TORUS vs Section 4: mirrors `MainThresholdsAPI.fixedInitialDensity`
  (`Contracts/V1/MainThresholds.lean`) at the single time exponent `q = 1`; the
  torus `prop:density` states only the `L¹_tH^s` case (`cor:mixed` supplies the
  other mixed norms), whereas the whole-space clause states `q ∈ {1,2}`
  together.

  Non-vacuity: `RelativelyDenseT` uses the registered `ℝ≥0∞`-valued
  `forceSobolevENormT`, never a `.toReal` collapse, and `breakdownSetT` demands
  an actual smooth compact torus force with `maximalLifespanT ν a f ≤ ofReal T`;
  `s < 1/2` is the full sub-critical range, including every negative order. -/
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

  /-- `03-torus.tex:355` and `04-whole-space.tex:8,13`: the sub-critical
  threshold `1/2` of `prop:density` is the registered `criticalOrder 1`
  (`= 2/1 - 3/2`).

  Exact quantifier order: none.  TORUS vs Section 4: identical value; this pins
  the torus threshold to the same arithmetic as `MainThresholdsAPI.thresholdValues`.

  Non-vacuity: a concrete real equality, not an opaque proposition. -/
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2

  /-- `03-torus.tex:358-361` (regular-reference case of the proof) and the
  distinction of `:626-631`: around every reference force that is regular
  through `T` (`RegularThroughT`, i.e. `T_max^ν(a,g) > T`), `thm:insertion`
  yields, at every sub-critical `s` and every positive radius `r`, a nearby
  torus force whose maximal lifespan is *exactly* `T` — sharper than the `≤ T`
  of `fixedInitialDensity`, which uses "breakdown by `T`" so that an
  already-earlier-breaking reference may be left unchanged.

  Exact quantifier order: `∀ a ∈ 𝓧, ∀ ν, 0 < ν, ∀ T, 0 < T, ∀ g ∈ 𝓕,
  RegularThroughT ν a g T → ∀ s, s < 1/2, ∀ r > 0, ∃ f ∈ 𝓕,
  ‖f - g‖_{L¹_tH^s} < r ∧ maximalLifespanT ν a f = ofReal T`.

  Non-vacuity: the lifespan conclusion is an exact `ℝ≥0∞` equality with
  `ofReal T` (the "singularity exactly at `T`" of `thm:insertion`), not the
  one-sided `≤` of the density set; `RegularThroughT` is the registered "regular
  through `T`" hypothesis and the norm is the registered `forceSobolevENormT`. -/
  regularReferenceSingular :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT → RegularThroughT ν a g T →
          ∀ s : ℝ, s < 1 / 2 → ∀ r : ℝ≥0∞, 0 < r →
            ∃ f ∈ forceClassT,
              forceSobolevENormT 1 s (fun z => f z - g z) < r ∧
                maximalLifespanT ν a f = ENNReal.ofReal T

/-! ## 2. `cor:mixed`, `03-torus.tex:528-539` -/

/-- **Corollary `cor:mixed` (a sufficient mixed-norm region),
`paper/sections/03-torus.tex:528-539`.**

`Prop`-valued: no constant or datum is introduced.  The corollary reuses the
two cases of `prop:density`; its only new content is the mixed-Lebesgue
topology and the region `eq:mixedregion`, controlled through the copied
`mixedLebesgueENormT` and the scaling exponent `α`. -/
structure MixedRegionAPI : Prop where
  /-- `03-torus.tex:530-535`, `eq:mixedregion`: for every fixed initial velocity
  the breakdown set is relatively dense in `𝓕` for the `L^q(0,∞;L^p(T³))`
  topology whenever `1 ≤ p, q ≤ ∞` and `3/p + 2/q > 3`.

  Exact quantifier order: `∀ a, a ∈ initialClassT → ∀ ν, 0 < ν → ∀ T, 0 < T →
  ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q → 3/p.toReal + 2/q.toReal > 3 →
  RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)`.  In `ℝ≥0∞` the
  upper bounds `p, q ≤ ∞` are automatic.

  TORUS vs Section 4: the whole-space development registers no mixed-Lebesgue
  density; this is a torus-only clause.

  Non-vacuity: `RelativelyDenseMixedT` uses the honest torus mixed Bochner norm
  `mixedLebesgueENormT` (an `⨅` over strongly measurable `L^p(T³)`-slice paths,
  so a missing representative reports `⊤`, not a spurious small distance);
  `1 ≤ p` is the carried `Fact`, `1 ≤ q` explicit, and the strict region is
  `eq:mixedregion` verbatim. -/
  mixedDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
          3 / p.toReal + 2 / q.toReal > 3 →
            RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)

  /-- `03-torus.tex:534-535` (proof of `cor:mixed`, `eq:Fclose`): on the region
  `3/p+2/q>3`, the packet scaling exponent `α(p,q) = -3 + 3/p + 2/q` and its
  shift `α(p,q)+1` are both strictly positive — precisely the fact that makes
  both terms of `‖g_ε-g‖_{L^q_tL^p} ≤ C(ε^{α} + ε^{α+1})` tend to zero.

  Exact quantifier order: `∀ (p q : ℝ≥0∞), 3/p.toReal + 2/q.toReal > 3 →
  0 < α(p,q) ∧ 0 < α(p,q)+1`, `α` the copied `alphaT` (= registered
  `Contracts.V1.alpha` by the file's drift check).

  Non-vacuity: a strict positivity of the concrete rate exponent, the analytic
  engine of the corollary; not a restatement of the region hypothesis (it turns
  the region into the two exponent signs used in `eq:Fclose`). -/
  regionPositive :
    ∀ (p q : ℝ≥0∞), 3 / p.toReal + 2 / q.toReal > 3 →
      0 < BlowupDensity.T15.Draft.alphaT p q ∧
        0 < BlowupDensity.T15.Draft.alphaT p q + 1

  /-- `03-torus.tex:536-538`: the two named spaces the region contains,
  `L¹_tL²_x` (`p=2, q=1`) and `L²_tL^{4/3}_x` (`p=4/3, q=2`), satisfy
  `eq:mixedregion`.

  Exact quantifier order: none; a conjunction of the two region inequalities at
  the two displayed exponent pairs.

  Non-vacuity: two concrete real inequalities (`3/2 + 2 = 7/2 > 3` and
  `9/4 + 1 = 13/4 > 3`), the paper's explicit "the sufficient region includes …"
  sentence, not an abstract proposition. -/
  regionExamples :
    (3 / (2 : ℝ) + 2 / (1 : ℝ) > 3) ∧ (3 / ((4 : ℝ) / 3) + 2 / (2 : ℝ) > 3)

/-! ## 3. `cor:closure`, `03-torus.tex:540-563` -/

/-- **Corollary `cor:closure` (strong closure in energy and dissipation),
`paper/sections/03-torus.tex:540-563`.**

`Prop`-valued: the approximating families are bound existentially inside the
fields.  This is the torus analogue of `CompletedDensityAPI.strongTrajectoryClosure`
(`Contracts/V1/CompletedDensity.lean`).  The proof consumes T18 `thm:insertion`
(`energyRate` for the `E_T` limit; `forceDifference_sobolev_bound` /
`forceDifference_negativeSobolev_tendsto` for the simultaneous `L¹_tH^s` limit;
`history`, `lifespan`, `blowup` for the trajectory data) plus the local
continuation of the reference (T11 `RegularThroughT`). -/
structure StrongClosureAPI : Prop where
  /-- `03-torus.tex:542-562`, `eq:closure`: every reference trajectory whose
  force `g` is a torus force smooth through `T` — realized as a classical
  solution `reference : ClassicalSolutionT ν a g (T+δ)` with `δ > 0` — is an
  `E_T`-limit of trajectories whose forces are torus forces smooth only on
  `[0,T)`, with finite `E_T` energy and unbounded maximum speed at `T`
  (`maximalLifespanT = ofReal T`); and for every sub-critical `s` the *same*
  approximating forces converge simultaneously in `L¹(0,∞;H^s(T³))`.

  Exact quantifier order: `∀ a ∈ 𝓧, ∀ ν, 0 < ν, ∀ T, 0 < T, ∀ g ∈ 𝓕,
  ∀ δ, 0 < δ, ∀ reference : ClassicalSolutionT ν a g (T+δ), ∃ ε₀ > 0,
  ∃ (u f : ℝ → SpaceTimeField), (∀ ε ∈ (0,ε₀]: torus force, exact lifespan `T`,
  finite `E_T`, a `ClassicalSolutionT` with `velocity = u ε`, and history
  `u ε = reference.velocity` on `[0, T-2ε²]`) ∧ (`E_T` limit of `u ε -
  reference.velocity`) ∧ (∀ s < 1/2: `L¹_tH^s` limit of `f ε - g`)`.

  TORUS vs Section 4: mirrors `strongTrajectoryClosure` field-for-field, with
  the torus `ClassicalSolutionT`, `energyENormT`, `forceSobolevENormT`, and
  `maximalLifespanT` in place of their `R` twins; the simultaneous force limit
  is the single inhomogeneous `L¹_tH^s` (`s < 1/2`) family here, rather than the
  summed `L¹_tH^0 + L²_tH^{-1} + L²_tḢ^{-1}` of the whole-space `prop:Renergy`.
  The extra `energyENormT T (u ε) < ⊤` conjunct is `:550-551` ("`u_ε` belongs to
  the specified ambient energy space").

  Non-vacuity: `ε₀ > 0` makes `(0,ε₀]` nonempty; each per-scale conjunct demands
  a genuine torus force, an exact registered lifespan `= ofReal T`, finite
  `E_T`, and a real `ClassicalSolutionT`; both limits are along the nontrivial
  filter `𝓝[>] 0` and share one existential family, so simultaneity cannot be
  discharged by unrelated approximants. -/
  strongClosure :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              ∃ ε₀ : ℝ, 0 < ε₀ ∧
                ∃ u f : ℝ → SpaceTimeField,
                  (∀ ε ∈ Ioc (0 : ℝ) ε₀,
                      f ε ∈ forceClassT ∧
                        maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                        energyENormT T (u ε) < ⊤ ∧
                        ∃ U : ClassicalSolutionT ν a (f ε) T,
                          U.velocity = u ε ∧
                          ∀ t ∈ Icc (0 : ℝ) (T - 2 * ε ^ 2), ∀ x : Space,
                            u ε (t, x) = reference.velocity (t, x)) ∧
                    Tendsto
                        (fun ε : ℝ =>
                          energyENormT T (fun z => u ε z - reference.velocity z))
                        (𝓝[>] 0) (𝓝 0) ∧
                    ∀ s : ℝ, s < 1 / 2 →
                      Tendsto
                        (fun ε : ℝ =>
                          forceSobolevENormT 1 s (fun z => f ε z - g z))
                        (𝓝[>] 0) (𝓝 0)

  /-- `03-torus.tex:550-551`: the reference itself has finite `E_T` energy — it
  is smooth through `T` (a classical solution on `[0,T+δ)` with `δ > 0`), hence
  bounded on the compact `[0,T] × T³`.  This anchors the `E_T` limit of
  `strongClosure` in a finite-distance ambient space.

  Exact quantifier order: `∀ a ∈ 𝓧, ∀ ν, 0 < ν, ∀ T, 0 < T, ∀ g ∈ 𝓕, ∀ δ,
  0 < δ, ∀ reference : ClassicalSolutionT ν a g (T+δ),
  energyENormT T reference.velocity < ⊤`.

  Non-vacuity: a strict finiteness in `ℝ≥0∞` of the registered energy norm of
  an actual solution velocity, not a vacuous bound. -/
  referenceFiniteEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              energyENormT T reference.velocity < ⊤

/-! ## 4. `prop:projection`, `03-torus.tex:564-631` -/

/-- **Proposition `prop:projection` (projection of extended singular data),
`paper/sections/03-torus.tex:564-631`.**

`Prop`-valued: the singular force over each datum is bound existentially inside
the fields.  Here `𝔅_{ν,T} = {(a,f) ∈ 𝓧 × 𝓕 : T_max^ν(a,f) ≤ T}`; the pair set
is not registered, so its three asserted properties are stated directly on the
components.  The proof consumes `prop:density` (`PeriodicDensityAPI`); the
`∀a∃f` order (`:616-619`) and the `a=0 ↦ {0}` fiber (`:572-573,619-622`) are
its two structural points. -/
structure ProjectionAPI : Prop where
  /-- `03-torus.tex:568-577`: `𝔅_{ν,T}` is dense in `𝓧 × 𝓕` for the product of
  any topology on `𝓧` and the relative `L¹(0,∞;H^s(T³))` topology on `𝓕`, for
  `s < 1/2`.  In a basic product neighbourhood `U × V` of `(a,g)` the datum `a`
  already lies in `U`, so density reduces to the `𝓕`-fibre: a nearby singular
  force `f` over the *same* `a`.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ a, a ∈ initialClassT →
  ∀ g ∈ 𝓕 → ∀ s, s < 1/2 → ∀ r > 0 → ∃ f ∈ 𝓕, ‖f - g‖_{L¹_tH^s} < r ∧
  maximalLifespanT ν a f ≤ ofReal T`, i.e. `(a,f) ∈ 𝔅_{ν,T} ∩ (U × V)`.

  Non-vacuity: `f` is a genuine torus force with the registered `ℝ≥0∞`
  `forceSobolevENormT` distance `< r` and lifespan `≤ ofReal T`; the same `a`
  threads both coordinates, so this is density of the *pair* set, not of `𝓕`
  alone. -/
  productDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ a : SpatialField, a ∈ initialClassT →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ s : ℝ, s < 1 / 2 → ∀ r : ℝ≥0∞, 0 < r →
            ∃ f : SpaceTimeField, f ∈ forceClassT ∧
              forceSobolevENormT 1 s (fun z => f z - g z) < r ∧
                maximalLifespanT ν a f ≤ ENNReal.ofReal T

  /-- `03-torus.tex:571-577`: the projection of `𝔅_{ν,T}` onto `𝓧` is all of
  `𝓧` — over every admissible initial velocity there is at least one singular
  force.  This is the `∀a∃f` surjectivity of `:616-619`.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → ∀ a, a ∈ initialClassT →
  ∃ f ∈ 𝓕, maximalLifespanT ν a f ≤ ofReal T`.  The `∀a` precedes the `∃f`, and
  the force may depend on `a`.

  Non-vacuity: for every datum a genuine torus force realizes membership of the
  pair set; the existential is over an actual `f ∈ forceClassT` with a lifespan
  bound, not an opaque proposition. -/
  projectionOntoInitial :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ a : SpatialField, a ∈ initialClassT →
        ∃ f : SpaceTimeField, f ∈ forceClassT ∧
          maximalLifespanT ν a f ≤ ENNReal.ofReal T

  /-- `03-torus.tex:572-573,619-622`: the family obtained while requiring `a=0`
  projects onto `𝓧` in the singleton `{0}`.  Concretely: `0` is an admissible
  initial velocity, and there is a singular force over it, so the `a=0` fibre of
  `𝔅_{ν,T}` is nonempty and its `𝓧`-projection is exactly `{0}` (the datum
  coordinate is pinned to `0`).  This is the contrast the paper draws with the
  `∀a∃f` surjectivity: `{0}` is not dense in a nontrivial initial-velocity space.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ T, 0 < T → (0 : SpatialField) ∈
  initialClassT ∧ ∃ f ∈ 𝓕, maximalLifespanT ν 0 f ≤ ofReal T`.

  Non-vacuity: the first conjunct certifies `{0} ⊆ 𝓧` (the zero field is smooth,
  periodic and divergence-free); the second gives an actual singular force over
  `0`, so the projected singleton is genuinely inhabited rather than empty. -/
  zeroInitialFiber :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      (0 : SpatialField) ∈ initialClassT ∧
        ∃ f : SpaceTimeField, f ∈ forceClassT ∧
          maximalLifespanT ν (0 : SpatialField) f ≤ ENNReal.ofReal T

/-! ## 5. Headline propositions, in the paper's quantifier order -/

/-- `03-torus.tex:350-357` `prop:density`, headline proposition. -/
def periodicDensityStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

/-- `03-torus.tex:530-535` `cor:mixed`, headline proposition. -/
def mixedRegionStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
        3 / p.toReal + 2 / q.toReal > 3 →
          RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)

/-- `03-torus.tex:542-562` `cor:closure`, headline proposition: the `E_T`
convergence of an approximating family with exact-lifespan singular forces
around every reference regular through `T`. -/
def strongClosureStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ g : SpaceTimeField, g ∈ forceClassT → ∀ δ : ℝ, 0 < δ →
        ∀ reference : ClassicalSolutionT ν a g (T + δ),
          ∃ ε₀ : ℝ, 0 < ε₀ ∧
            ∃ u f : ℝ → SpaceTimeField,
              (∀ ε ∈ Ioc (0 : ℝ) ε₀,
                f ε ∈ forceClassT ∧
                  maximalLifespanT ν a (f ε) = ENNReal.ofReal T) ∧
                Tendsto
                  (fun ε : ℝ =>
                    energyENormT T (fun z => u ε z - reference.velocity z))
                  (𝓝[>] 0) (𝓝 0)

/-- `03-torus.tex:571-577` `prop:projection`, headline proposition: the `∀a∃f`
projection of the extended singular-data set onto `𝓧`. -/
def projectionStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ a : SpatialField, a ∈ initialClassT →
      ∃ f : SpaceTimeField, f ∈ forceClassT ∧
        maximalLifespanT ν a f ≤ ENNReal.ofReal T

end BlowupDensity.T19.DraftB
