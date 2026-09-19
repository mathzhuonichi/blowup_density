import NSFormalization.Section3.T19.Bookkeeping
import NSFormalization.Section4.A02.Patch

/-!
# T19 canonical density package on `T³`

This module restates the four reconciled T19 records from
`research/T19/Spec.lean` over the canonical Section 3 vocabulary.  It follows
the approved B/B/A/A bases: all four records are `Prop`-valued, the T18
insertion record is not threaded, density is expressed by
`RelativelyDenseT`, the mixed exponent is the canonical `T15.alphaT`, and no
honesty guards are added.

The records cover `prop:density` (`03-torus.tex:349-368`), `cor:mixed`
(`:528-538`), `cor:closure` (`:540-561`), and `prop:projection` (`:564-590`).
-/

noncomputable section

namespace NSFormalization.Section3.T19

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Section3.T10
open scoped ENNReal Topology BigOperators

/-! ## Paper-local sets and norms -/

/-- `03-torus.tex:541`: `R_{a,T}`, the trajectories with initial velocity `a`
and a force in `𝓕` that are smooth through `T`. -/
def RegularTrajectoryT (ν : ℝ) (a : SpatialField) (T : ℝ)
    (u : SpaceTimeField) : Prop :=
  ∃ g : SpaceTimeField, g ∈ forceClassT ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a g (T + δ), w.velocity = u

/-- `03-torus.tex:542`: `S_{a,T}`, the finite-energy trajectories smooth on
`[0,T)` whose maximum speed is unbounded at `T`. -/
def SingularTrajectoryT (ν : ℝ) (a : SpatialField) (T : ℝ)
    (u : SpaceTimeField) : Prop :=
  ∃ g : SpaceTimeField, g ∈ forceClassT ∧
    (∃ w : ClassicalSolutionT ν a g T, w.velocity = u) ∧
    energyENormT T u ≠ ⊤ ∧
    NSFormalization.Section4.A02.limsupLeft T
        (fun t => NSFormalization.Section4.A02.speedENorm
          (fun x : Space => u (t, x))) = ⊤

/-- `03-torus.tex:565-568`: the extended singular-data set
`𝔅_{ν,T} = {(a,f) ∈ 𝓧×𝓕 : T_max^ν(a,f) ≤ T}`. -/
def extendedBreakdownSetT (ν T : ℝ) : Set (SpatialField × SpaceTimeField) :=
  {p | p.1 ∈ initialClassT ∧ p.2 ∈ forceClassT ∧
    maximalLifespanT ν p.1 p.2 ≤ ENNReal.ofReal T}

/-- `03-torus.tex:529-531`: relative density in the periodic
`L^q(0,∞;L^p(T³))` pseudometric. -/
def RelativelyDenseMixedT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Y S : Set SpaceTimeField) : Prop :=
  ∀ g ∈ Y, ∀ r : ℝ≥0∞, 0 < r →
    ∃ f ∈ S, mixedLebesgueENormT q p (fun z => f z - g z) < r

/-! ## `prop:density` (`03-torus.tex:349-368`), base B -/

/-- **`prop:density` — density for each fixed initial velocity,
`paper/sections/03-torus.tex:349-356`, proof `:357-368`.**

For `a ∈ 𝓧`, `ν>0`, `T>0`, and `s<1/2`, every force in `𝓕` is approximated
in the relative `L¹_tH^s_x` topology by a force whose maximal lifespan is at
most `T`.  The sharp regular-reference clause records the exact lifespan
conclusion supplied by `thm:insertion`. -/
structure PeriodicDensityAPI : Prop where
  /-- `03-torus.tex:350-355`: the headline fixed-initial-data density
  proposition, with the paper's quantifier order. -/
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

  /-- `03-torus.tex:350`: the displayed threshold is the canonical critical
  order at time exponent one. -/
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2

  /-- `03-torus.tex:363-365,590`: near a reference regular through `T`, the
  insertion conclusion has lifespan exactly `T`, not merely at most `T`. -/
  regularReferenceSingular :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT → RegularThroughT ν a g T →
          ∀ s : ℝ, s < 1 / 2 → ∀ r : ℝ≥0∞, 0 < r →
            ∃ f ∈ forceClassT,
              forceSobolevENormT 1 s (fun z => f z - g z) < r ∧
                maximalLifespanT ν a f = ENNReal.ofReal T

/-- **`prop:density` in the paper's quantifier order,
`03-torus.tex:350-355`.** -/
def periodicDensityStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

/-! ## `cor:mixed` (`03-torus.tex:528-538`), base B -/

/-- **`cor:mixed` — the sufficient mixed-norm region,
`paper/sections/03-torus.tex:528-533`, proof `:534-536`.**

For fixed `a ∈ 𝓧`, the breakdown set is dense in the relative
`L^q_tL^p_x` topology whenever `1≤p,q≤∞` and `3/p+2/q>3`. -/
structure MixedRegionAPI : Prop where
  /-- `03-torus.tex:529-531`, `eq:mixedregion`: mixed-norm density throughout
  the stated sufficient region. -/
  mixedDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
          3 < 3 / p.toReal + 2 / q.toReal →
            RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)

  /-- `03-torus.tex:535-536`: positivity of both powers in `eq:Fclose`. -/
  mixedRegionArithmetic :
    ∀ p q : ℝ≥0∞, 3 < 3 / p.toReal + 2 / q.toReal →
      0 < NSFormalization.Section3.T15.alphaT p q ∧
        0 < NSFormalization.Section3.T15.alphaT p q + 1

  /-- `03-torus.tex:538`: the region contains `L¹_tL²_x` and
  `L²_tL^(4/3)_x`. -/
  regionExamples :
    0 < NSFormalization.Section3.T15.alphaT 2 1 ∧
      0 < NSFormalization.Section3.T15.alphaT (4 / 3) 2

/-- **`cor:mixed` in the paper's quantifier order,
`03-torus.tex:529-531`.** -/
def mixedRegionStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
        3 < 3 / p.toReal + 2 / q.toReal →
          RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)

/-! ## `cor:closure` (`03-torus.tex:540-561`), base A -/

/-- **`cor:closure` — strong closure in energy and dissipation,
`paper/sections/03-torus.tex:540-549`, proof `:552-561`.**

Regular trajectories lie in the `E_T`-closure of singular trajectories, and
the insertion family converges simultaneously in trajectory energy and in
the subcritical force topology. -/
structure StrongClosureAPI : Prop where
  /-- `03-torus.tex:556-560`: the finite-time `L²_tL²_x` embedding used to
  identify the closure topology. -/
  energyTimeEmbedding :
    ∀ T : ℝ, 0 < T → ∀ z : SpaceTimeField,
      spaceTimeL2L2ENormT T z ≤
        ENNReal.ofReal (Real.sqrt T) * energyEssSupT T z

  /-- `03-torus.tex:543-545`, `eq:closure`: `R_{a,T}` is contained in the
  `E_T`-closure of `S_{a,T}`, in epsilon-approximation form. -/
  closureInEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
              energyENormT T (fun z => u z - u' z) < r

  /-- `03-torus.tex:546-549`: simultaneous convergence of the inserted
  solution-force pairs to a regular reference pair. -/
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

  /-- `03-torus.tex:554`: a reference smooth through `T` has finite `E_T`
  energy. -/
  referenceFiniteEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              energyENormT T reference.velocity < ⊤

/-- **`cor:closure` `eq:closure` in the paper's quantifier order,
`03-torus.tex:543-545`.** -/
def strongClosureStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
        ∀ r : ℝ≥0∞, 0 < r →
          ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
            energyENormT T (fun z => u z - u' z) < r

/-! ## `prop:projection` (`03-torus.tex:564-590`), base A -/

/-- **`prop:projection` — projection of extended singular data,
`paper/sections/03-torus.tex:564-571`, proof `:573-576`, remarks `:579-590`.**

The extended breakdown set is dense in the force factor while keeping the
initial datum fixed, projects onto all of `𝓧`, and its zero-initial subfamily
projects to `{0}`. -/
structure ProjectionAPI : Prop where
  /-- `03-torus.tex:570,573-575`: product density with the initial datum kept
  fixed. -/
  extendedProductDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        ∀ a : SpatialField, a ∈ initialClassT →
          ∀ g : SpaceTimeField, g ∈ forceClassT →
            ∀ r : ℝ≥0∞, 0 < r →
              ∃ f : SpaceTimeField,
                (a, f) ∈ extendedBreakdownSetT ν T ∧
                  forceSobolevENormT 1 s (fun z => f z - g z) < r

  /-- `03-torus.tex:570,579`: the projection has the paper's `∀a∃f`
  content and equals the full initial class. -/
  projectionOntoInitialData :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst '' (extendedBreakdownSetT ν T) = initialClassT

  /-- `03-torus.tex:571,586`: imposing `a=0` instead projects to the
  nonempty singleton `{0}`. -/
  zeroInitialProjection :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst ''
          {p : SpatialField × SpaceTimeField |
            p ∈ extendedBreakdownSetT ν T ∧ p.1 = (fun _ => 0)} =
        {(fun _ => 0 : SpatialField)}

/-- **`prop:projection` in the paper's quantifier order,
`03-torus.tex:565-571`.** -/
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

/-! ## Already proved (lane 388, U1--U6)

These examples deliberately restate the record-field types.  Thus the later
U-REG assembly can fill the five already-proved fields by theorem name; the
two U6 zero-representative helpers are checked in the exact types consumed by
the density dichotomies.
-/

example : criticalOrder 1 = (1 : ℝ) / 2 := thresholdValue

example :
    ∀ p q : ℝ≥0∞, 3 < 3 / p.toReal + 2 / q.toReal →
      0 < NSFormalization.Section3.T15.alphaT p q ∧
        0 < NSFormalization.Section3.T15.alphaT p q + 1 :=
  mixedRegionArithmetic

example :
    0 < NSFormalization.Section3.T15.alphaT 2 1 ∧
      0 < NSFormalization.Section3.T15.alphaT (4 / 3) 2 :=
  regionExamples

example :
    ∀ T : ℝ, 0 < T → ∀ z : SpaceTimeField,
      spaceTimeL2L2ENormT T z ≤
        ENNReal.ofReal (Real.sqrt T) * energyEssSupT T z :=
  energyTimeEmbedding

example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              energyENormT T reference.velocity < ⊤ :=
  referenceFiniteEnergy

example (q : ℝ≥0∞) (s : ℝ) :
    forceSobolevENormT q s (0 : SpaceTimeField) = 0 :=
  torusForceSobolevENorm_zero q s

example (q p : ℝ≥0∞) [Fact (1 ≤ p)] :
    mixedLebesgueENormT q p (0 : SpaceTimeField) = 0 :=
  torusMixedLebesgueENormT_zero q p

end NSFormalization.Section3.T19
