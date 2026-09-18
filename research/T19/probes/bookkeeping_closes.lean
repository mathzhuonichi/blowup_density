import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.MainThresholds
import Contracts.V1.Data
import Contracts.V1.Correction
import Bindings.TorusLocalTheory
import NSFormalization.Section3.T19.Bookkeeping

/-!
# T19 U1--U6 contract conformance probe

The two unregistered mixed-norm carriers and the local space-time norm below
are copied from `research/T19/Spec.lean`.  Each bookkeeping field is then
closed directly by its canonical theorem.  The intervening equality checks
record that the registered spellings are definitionally the canonical ones.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal Topology BigOperators

namespace BlowupDensity.T15.Draft

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

namespace BlowupDensity.T19

/-- `03-torus.tex:558`: the torus `L²(0,T;L²(T³))` extended norm. -/
def spaceTimeL2L2ENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (torusLift (fun x => z (t, x))) 2 periodicTorusMeasure) ^ (2 : ℝ))
    ^ ((2 : ℝ)⁻¹)

end BlowupDensity.T19

namespace NSFormalization.Section3.T19.Probe

/-! The registered vocabulary has the canonical implementation by reduction. -/

example (q : ℝ) :
    BlowupDensity.Contracts.V1.Data.criticalOrder q =
      NSFormalization.Section3.T19.criticalOrder q := rfl

example (p q : ℝ≥0∞) :
    BlowupDensity.Contracts.V1.alpha p q =
      NSFormalization.Section3.T15.alphaT p q := rfl

example (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) :
    forceSobolevENormT q s f =
      NSFormalization.Section3.T10.forceSobolevENormT q s f := rfl

example (T : ℝ) (z : SpaceTimeField) :
    energyEssSupT T z = NSFormalization.Section3.T10.energyEssSupT T z := rfl

example (T : ℝ) (z : SpaceTimeField) :
    energyENormT T z = NSFormalization.Section3.T10.energyENormT T z := rfl

example (q p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField) :
    BlowupDensity.T15.Draft.mixedLebesgueENormT q p f =
      NSFormalization.Section3.T19.mixedLebesgueENormT q p f := rfl

example (T : ℝ) (z : SpaceTimeField) :
    BlowupDensity.T19.spaceTimeL2L2ENormT T z =
      NSFormalization.Section3.T19.spaceTimeL2L2ENormT T z := rfl

/-! U1: `PeriodicDensityAPI.thresholdValue`. -/

example : BlowupDensity.Contracts.V1.Data.criticalOrder 1 = (1 : ℝ) / 2 := by
  exact NSFormalization.Section3.T19.thresholdValue

/-! U2: `MixedRegionAPI.mixedRegionArithmetic`. -/

example :
    ∀ p q : ℝ≥0∞, 3 < 3 / p.toReal + 2 / q.toReal →
      0 < BlowupDensity.Contracts.V1.alpha p q ∧
        0 < BlowupDensity.Contracts.V1.alpha p q + 1 := by
  exact NSFormalization.Section3.T19.mixedRegionArithmetic

/-! A concrete U2 instance at `(p,q)=(2,1)`. -/

example :
    0 < BlowupDensity.Contracts.V1.alpha 2 1 ∧
      0 < BlowupDensity.Contracts.V1.alpha 2 1 + 1 := by
  exact NSFormalization.Section3.T19.mixedRegionArithmetic 2 1 (by norm_num)

/-! U3: `MixedRegionAPI.regionExamples`, including both numeric instances. -/

example :
    0 < BlowupDensity.Contracts.V1.alpha 2 1 ∧
      0 < BlowupDensity.Contracts.V1.alpha (4 / 3) 2 := by
  exact NSFormalization.Section3.T19.regionExamples

/-! U4: `StrongClosureAPI.energyTimeEmbedding`. -/

example :
    ∀ T : ℝ, 0 < T → ∀ z : SpaceTimeField,
      BlowupDensity.T19.spaceTimeL2L2ENormT T z ≤
        ENNReal.ofReal (Real.sqrt T) * energyEssSupT T z := by
  exact NSFormalization.Section3.T19.energyTimeEmbedding

/-! U5: `StrongClosureAPI.referenceFiniteEnergy`. -/

example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              energyENormT T reference.velocity < ⊤ := by
  intro a ha ν hν T hT g hg δ hδ reference
  exact NSFormalization.Section3.T19.referenceFiniteEnergy
    a ha ν hν T hT g hg δ hδ
      (BlowupDensity.Bindings.TorusLocalTheory.ofContract reference)

/-! U6: the two zero-representative helpers in registered spellings. -/

example (q : ℝ≥0∞) (s : ℝ) :
    forceSobolevENormT q s (0 : SpaceTimeField) = 0 := by
  exact NSFormalization.Section3.T19.torusForceSobolevENorm_zero q s

example (q p : ℝ≥0∞) [Fact (1 ≤ p)] :
    BlowupDensity.T15.Draft.mixedLebesgueENormT q p (0 : SpaceTimeField) = 0 := by
  exact NSFormalization.Section3.T19.torusMixedLebesgueENormT_zero q p

end NSFormalization.Section3.T19.Probe
