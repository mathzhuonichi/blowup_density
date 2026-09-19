import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.MainThresholds
import Contracts.V1.CompletedDensity
import Contracts.V1.Data
import Contracts.V1.MaximalPartial
import Contracts.V1.Correction
import Bindings.TorusData
import Bindings.TorusLocalTheory
import Bindings.MaximalPartial
import NSFormalization.Section3.T19.Density

/-!
# T19 canonical-record probe

The `BlowupDensity.T19` block below is synchronized with
`research/T19/Spec.lean`: its declarations are copied verbatim, omitting only
docstrings.  Research files are not a Lake library and therefore cannot be
imported as modules by this standalone probe; the copied block is the same
house pattern used by the T17 and T20 canonical probes.

The final section checks every vocabulary rename and gives fieldwise
conversions in both directions for all four records.  The
`ClassicalSolutionT` structure is transported with
`Bindings.TorusLocalTheory.toContract` / `ofContract`.  In particular,
`maximalLifespanT` is deliberately *not* an `rfl` drift check: it uses
`Bindings.TorusLocalTheory.maximalLifespanT_eq`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal Topology BigOperators

/-! ## Synchronized Spec declarations -/

namespace BlowupDensity.T15.Draft

def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

end BlowupDensity.T15.Draft

namespace BlowupDensity.T19

open BlowupDensity.T15.Draft

def RegularTrajectoryT (ν : ℝ) (a : SpatialField) (T : ℝ)
    (u : SpaceTimeField) : Prop :=
  ∃ g : SpaceTimeField, g ∈ forceClassT ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a g (T + δ), w.velocity = u

def SingularTrajectoryT (ν : ℝ) (a : SpatialField) (T : ℝ)
    (u : SpaceTimeField) : Prop :=
  ∃ g : SpaceTimeField, g ∈ forceClassT ∧
    (∃ w : ClassicalSolutionT ν a g T, w.velocity = u) ∧
    energyENormT T u ≠ ⊤ ∧
    BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft T
        (fun t => BlowupDensity.Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => u (t, x))) = ⊤

def extendedBreakdownSetT (ν T : ℝ) : Set (SpatialField × SpaceTimeField) :=
  {p | p.1 ∈ initialClassT ∧ p.2 ∈ forceClassT ∧
    maximalLifespanT ν p.1 p.2 ≤ ENNReal.ofReal T}

def spaceTimeL2L2ENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (torusLift (fun x => z (t, x))) 2 periodicTorusMeasure) ^ (2 : ℝ))
    ^ ((2 : ℝ)⁻¹)

def RelativelyDenseMixedT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Y S : Set SpaceTimeField) : Prop :=
  ∀ g ∈ Y, ∀ r : ℝ≥0∞, 0 < r →
    ∃ f ∈ S,
      BlowupDensity.T15.Draft.mixedLebesgueENormT q p (fun z => f z - g z) < r

structure PeriodicDensityAPI : Prop where
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2
  regularReferenceSingular :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT → RegularThroughT ν a g T →
          ∀ s : ℝ, s < 1 / 2 → ∀ r : ℝ≥0∞, 0 < r →
            ∃ f ∈ forceClassT,
              forceSobolevENormT 1 s (fun z => f z - g z) < r ∧
                maximalLifespanT ν a f = ENNReal.ofReal T

def periodicDensityStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

structure MixedRegionAPI : Prop where
  mixedDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
          3 < 3 / p.toReal + 2 / q.toReal →
            RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)
  mixedRegionArithmetic :
    ∀ p q : ℝ≥0∞, 3 < 3 / p.toReal + 2 / q.toReal →
      0 < BlowupDensity.Contracts.V1.alpha p q ∧
        0 < BlowupDensity.Contracts.V1.alpha p q + 1
  regionExamples :
    0 < BlowupDensity.Contracts.V1.alpha 2 1 ∧
      0 < BlowupDensity.Contracts.V1.alpha (4 / 3) 2

def mixedRegionStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
        3 < 3 / p.toReal + 2 / q.toReal →
          RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)

structure StrongClosureAPI : Prop where
  energyTimeEmbedding :
    ∀ T : ℝ, 0 < T → ∀ z : SpaceTimeField,
      spaceTimeL2L2ENormT T z ≤
        ENNReal.ofReal (Real.sqrt T) * energyEssSupT T z
  closureInEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
              energyENormT T (fun z => u z - u' z) < r
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
  referenceFiniteEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              energyENormT T reference.velocity < ⊤

def strongClosureStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
        ∀ r : ℝ≥0∞, 0 < r →
          ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
            energyENormT T (fun z => u z - u' z) < r

structure ProjectionAPI : Prop where
  extendedProductDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        ∀ a : SpatialField, a ∈ initialClassT →
          ∀ g : SpaceTimeField, g ∈ forceClassT →
            ∀ r : ℝ≥0∞, 0 < r →
              ∃ f : SpaceTimeField,
                (a, f) ∈ extendedBreakdownSetT ν T ∧
                  forceSobolevENormT 1 s (fun z => f z - g z) < r
  projectionOntoInitialData :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst '' (extendedBreakdownSetT ν T) = initialClassT
  zeroInitialProjection :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst ''
          {p : SpatialField × SpaceTimeField |
            p ∈ extendedBreakdownSetT ν T ∧ p.1 = (fun _ => 0)} =
        {(fun _ => 0 : SpatialField)}

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

/-! ## Drift checks and fieldwise conversions -/

namespace T19CanonicalProbe

/-! ### Definition-level drift checks -/

theorem criticalOrder_eq :
    @BlowupDensity.Contracts.V1.Data.criticalOrder =
      @NSFormalization.Section3.T19.criticalOrder := rfl

theorem alpha_eq :
    @BlowupDensity.Contracts.V1.alpha =
      @NSFormalization.Section3.T15.alphaT := rfl

theorem periodicTorusMeasure_eq :
    BlowupDensity.Contracts.V1.TorusData.periodicTorusMeasure =
      NSFormalization.Section3.T10.periodicTorusMeasure := rfl

theorem torusLift_eq {E : Type*} (f : Space → E)
    (z : BlowupDensity.Contracts.V1.TorusData.PeriodicTorus) :
    BlowupDensity.Contracts.V1.TorusData.torusLift f z =
      NSFormalization.Section3.T10.torusLift f z := rfl

theorem initialClassT_eq :
    initialClassT = NSFormalization.Section3.T10.initialClassT := rfl

theorem forceClassT_eq :
    forceClassT = NSFormalization.Section3.T10.forceClassT := rfl

theorem forceSobolevENormT_eq (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) :
    forceSobolevENormT q s f =
      NSFormalization.Section3.T10.forceSobolevENormT q s f := rfl

theorem relativelyDenseT_eq (q : ℝ≥0∞) (s : ℝ)
    (Y S : Set SpaceTimeField) :
    RelativelyDenseT q s Y S =
      NSFormalization.Section3.T10.RelativelyDenseT q s Y S := rfl

theorem energyEssSupT_eq (T : ℝ) (z : SpaceTimeField) :
    energyEssSupT T z = NSFormalization.Section3.T10.energyEssSupT T z := rfl

theorem energyENormT_eq (T : ℝ) (z : SpaceTimeField) :
    energyENormT T z = NSFormalization.Section3.T10.energyENormT T z := rfl

theorem mixedSlicePath_eq :
    @BlowupDensity.T15.Draft.IsPeriodicLebesgueSlicePath =
      @NSFormalization.Section3.T19.IsPeriodicLebesgueSlicePath := rfl

theorem mixedLebesgueENormT_eq :
    @BlowupDensity.T15.Draft.mixedLebesgueENormT =
      @NSFormalization.Section3.T19.mixedLebesgueENormT := rfl

theorem spaceTimeL2L2ENormT_eq :
    @BlowupDensity.T19.spaceTimeL2L2ENormT =
      @NSFormalization.Section3.T19.spaceTimeL2L2ENormT := rfl

theorem relativelyDenseMixedT_eq :
    @BlowupDensity.T19.RelativelyDenseMixedT =
      @NSFormalization.Section3.T19.RelativelyDenseMixedT := rfl

theorem limsupLeft_eq :
    @BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft =
      @NSFormalization.Section4.A02.limsupLeft := rfl

theorem speedENorm_eq :
    @BlowupDensity.Contracts.V1.MaximalPartial.speedENorm =
      @NSFormalization.Section4.A02.speedENorm := rfl

/-- This bridge is not `rfl`: the two `ClassicalSolutionT` structures are
distinct inductive types, so equality of their lifespan suprema is proved
through `BTL.ofContract` / `BTL.toContract`. -/
theorem maximalLifespanT_eq (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) :
    maximalLifespanT ν a f =
      NSFormalization.Section3.T10.maximalLifespanT ν a f :=
  BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq ν a f

theorem regularThroughT_eq (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (T : ℝ) :
    RegularThroughT ν a f T =
      NSFormalization.Section3.T10.RegularThroughT ν a f T :=
  BlowupDensity.Bindings.TorusLocalTheory.regularThroughT_eq ν a f T

theorem breakdownSetT_eq (ν : ℝ) (a : SpatialField) (T : ℝ) :
    breakdownSetT ν a T = NSFormalization.Section3.T10.breakdownSetT ν a T :=
  BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq ν a T

example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionT ν a f T) :
    (BlowupDensity.Bindings.TorusLocalTheory.ofContract w).velocity = w.velocity := rfl

example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section3.T10.ClassicalSolutionT ν a f T) :
    (BlowupDensity.Bindings.TorusLocalTheory.toContract w).velocity = w.velocity := rfl

example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionT ν a f T) :
    BlowupDensity.Bindings.TorusLocalTheory.toContract
      (BlowupDensity.Bindings.TorusLocalTheory.ofContract w) = w := rfl

example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section3.T10.ClassicalSolutionT ν a f T) :
    BlowupDensity.Bindings.TorusLocalTheory.ofContract
      (BlowupDensity.Bindings.TorusLocalTheory.toContract w) = w := rfl

/-! ### Paper-local proposition transports -/

theorem regularTrajectoryT_iff (ν : ℝ) (a : SpatialField) (T : ℝ)
    (u : SpaceTimeField) :
    BlowupDensity.T19.RegularTrajectoryT ν a T u ↔
      NSFormalization.Section3.T19.RegularTrajectoryT ν a T u := by
  constructor
  · rintro ⟨g, hg, δ, hδ, w, hw⟩
    exact ⟨g, hg, δ, hδ, BlowupDensity.Bindings.TorusLocalTheory.ofContract w, hw⟩
  · rintro ⟨g, hg, δ, hδ, w, hw⟩
    exact ⟨g, hg, δ, hδ, BlowupDensity.Bindings.TorusLocalTheory.toContract w, hw⟩

theorem singularTrajectoryT_iff (ν : ℝ) (a : SpatialField) (T : ℝ)
    (u : SpaceTimeField) :
    BlowupDensity.T19.SingularTrajectoryT ν a T u ↔
      NSFormalization.Section3.T19.SingularTrajectoryT ν a T u := by
  constructor
  · rintro ⟨g, hg, ⟨w, hw⟩, henergy, hblow⟩
    exact ⟨g, hg, ⟨BlowupDensity.Bindings.TorusLocalTheory.ofContract w, hw⟩,
      henergy, hblow⟩
  · rintro ⟨g, hg, ⟨w, hw⟩, henergy, hblow⟩
    exact ⟨g, hg, ⟨BlowupDensity.Bindings.TorusLocalTheory.toContract w, hw⟩,
      henergy, hblow⟩

theorem extendedBreakdownSetT_eq (ν T : ℝ) :
    BlowupDensity.T19.extendedBreakdownSetT ν T =
      NSFormalization.Section3.T19.extendedBreakdownSetT ν T := by
  ext p
  simp only [BlowupDensity.T19.extendedBreakdownSetT,
    NSFormalization.Section3.T19.extendedBreakdownSetT, Set.mem_ofPred_eq]
  rw [BlowupDensity.Bindings.TorusLocalTheory.initialClassT_eq,
    BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
    BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq]

/-! ### `PeriodicDensityAPI` -/

theorem periodicToCanonical (h : BlowupDensity.T19.PeriodicDensityAPI) :
    NSFormalization.Section3.T19.PeriodicDensityAPI where
  fixedInitialDensity := by
    intro a ha ν hν T hT s hs
    have hd := h.fixedInitialDensity a ha ν hν T hT s hs
    rw [BlowupDensity.Bindings.TorusLocalTheory.relativelyDenseT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq] at hd
    exact hd
  thresholdValue := h.thresholdValue
  regularReferenceSingular := by
    intro a ha ν hν T hT g hg hreg s hs r hr
    have hreg' : RegularThroughT ν a g T := by
      rw [BlowupDensity.Bindings.TorusLocalTheory.regularThroughT_eq]
      exact hreg
    obtain ⟨f, hf, hdist, hlife⟩ :=
      h.regularReferenceSingular a ha ν hν T hT g hg hreg' s hs r hr
    refine ⟨f, hf, hdist, ?_⟩
    rw [← BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq]
    exact hlife

theorem periodicOfCanonical (h : NSFormalization.Section3.T19.PeriodicDensityAPI) :
    BlowupDensity.T19.PeriodicDensityAPI where
  fixedInitialDensity := by
    intro a ha ν hν T hT s hs
    rw [BlowupDensity.Bindings.TorusLocalTheory.relativelyDenseT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq]
    exact h.fixedInitialDensity a ha ν hν T hT s hs
  thresholdValue := h.thresholdValue
  regularReferenceSingular := by
    intro a ha ν hν T hT g hg hreg s hs r hr
    have hreg' : NSFormalization.Section3.T10.RegularThroughT ν a g T := by
      rw [← BlowupDensity.Bindings.TorusLocalTheory.regularThroughT_eq]
      exact hreg
    obtain ⟨f, hf, hdist, hlife⟩ :=
      h.regularReferenceSingular a ha ν hν T hT g hg hreg' s hs r hr
    refine ⟨f, hf, hdist, ?_⟩
    rw [BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq]
    exact hlife

/-! ### `MixedRegionAPI` -/

theorem mixedToCanonical (h : BlowupDensity.T19.MixedRegionAPI) :
    NSFormalization.Section3.T19.MixedRegionAPI where
  mixedDensity := by
    intro a ha ν hν T hT p q _ hq hregion
    have hd := h.mixedDensity a ha ν hν T hT p q hq hregion
    rw [relativelyDenseMixedT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq] at hd
    exact hd
  mixedRegionArithmetic := h.mixedRegionArithmetic
  regionExamples := h.regionExamples

theorem mixedOfCanonical (h : NSFormalization.Section3.T19.MixedRegionAPI) :
    BlowupDensity.T19.MixedRegionAPI where
  mixedDensity := by
    intro a ha ν hν T hT p q _ hq hregion
    rw [relativelyDenseMixedT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq]
    exact h.mixedDensity a ha ν hν T hT p q hq hregion
  mixedRegionArithmetic := h.mixedRegionArithmetic
  regionExamples := h.regionExamples

/-! ### `StrongClosureAPI` -/

theorem strongToCanonical (h : BlowupDensity.T19.StrongClosureAPI) :
    NSFormalization.Section3.T19.StrongClosureAPI where
  energyTimeEmbedding := h.energyTimeEmbedding
  closureInEnergy := by
    intro a ha ν hν T hT u hregular r hr
    obtain ⟨u', hsingular, hdist⟩ :=
      h.closureInEnergy a ha ν hν T hT u
        ((regularTrajectoryT_iff ν a T u).mpr hregular) r hr
    exact ⟨u', (singularTrajectoryT_iff ν a T u').mp hsingular, hdist⟩
  simultaneousPairConvergence := by
    intro a ha ν hν T hT g hg δ hδ reference
    obtain ⟨ε₀, hε₀, u, f, hper, henergy, hforce⟩ :=
      h.simultaneousPairConvergence a ha ν hν T hT g hg δ hδ
        (BlowupDensity.Bindings.TorusLocalTheory.toContract reference)
    refine ⟨ε₀, hε₀, u, f, ?_, henergy, hforce⟩
    intro ε hε
    obtain ⟨hf, hlife, ⟨w, hw⟩, hsingular⟩ := hper ε hε
    refine ⟨hf, ?_,
      ⟨BlowupDensity.Bindings.TorusLocalTheory.ofContract w, hw⟩,
      (singularTrajectoryT_iff ν a T (u ε)).mp hsingular⟩
    rw [← BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq]
    exact hlife
  referenceFiniteEnergy := by
    intro a ha ν hν T hT g hg δ hδ reference
    exact h.referenceFiniteEnergy a ha ν hν T hT g hg δ hδ
      (BlowupDensity.Bindings.TorusLocalTheory.toContract reference)

theorem strongOfCanonical (h : NSFormalization.Section3.T19.StrongClosureAPI) :
    BlowupDensity.T19.StrongClosureAPI where
  energyTimeEmbedding := h.energyTimeEmbedding
  closureInEnergy := by
    intro a ha ν hν T hT u hregular r hr
    obtain ⟨u', hsingular, hdist⟩ :=
      h.closureInEnergy a ha ν hν T hT u
        ((regularTrajectoryT_iff ν a T u).mp hregular) r hr
    exact ⟨u', (singularTrajectoryT_iff ν a T u').mpr hsingular, hdist⟩
  simultaneousPairConvergence := by
    intro a ha ν hν T hT g hg δ hδ reference
    obtain ⟨ε₀, hε₀, u, f, hper, henergy, hforce⟩ :=
      h.simultaneousPairConvergence a ha ν hν T hT g hg δ hδ
        (BlowupDensity.Bindings.TorusLocalTheory.ofContract reference)
    refine ⟨ε₀, hε₀, u, f, ?_, henergy, hforce⟩
    intro ε hε
    obtain ⟨hf, hlife, ⟨w, hw⟩, hsingular⟩ := hper ε hε
    refine ⟨hf, ?_,
      ⟨BlowupDensity.Bindings.TorusLocalTheory.toContract w, hw⟩,
      (singularTrajectoryT_iff ν a T (u ε)).mpr hsingular⟩
    rw [BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq]
    exact hlife
  referenceFiniteEnergy := by
    intro a ha ν hν T hT g hg δ hδ reference
    exact h.referenceFiniteEnergy a ha ν hν T hT g hg δ hδ
      (BlowupDensity.Bindings.TorusLocalTheory.ofContract reference)

/-! ### `ProjectionAPI` -/

theorem projectionToCanonical (h : BlowupDensity.T19.ProjectionAPI) :
    NSFormalization.Section3.T19.ProjectionAPI where
  extendedProductDensity := by
    intro ν hν T hT s hs a ha g hg r hr
    obtain ⟨f, hmem, hdist⟩ :=
      h.extendedProductDensity ν hν T hT s hs a ha g hg r hr
    exact ⟨f, by rwa [extendedBreakdownSetT_eq] at hmem, hdist⟩
  projectionOntoInitialData := by
    intro ν hν T hT
    simpa only [extendedBreakdownSetT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.initialClassT_eq] using
      h.projectionOntoInitialData ν hν T hT
  zeroInitialProjection := by
    intro ν hν T hT
    simpa only [extendedBreakdownSetT_eq] using h.zeroInitialProjection ν hν T hT

theorem projectionOfCanonical (h : NSFormalization.Section3.T19.ProjectionAPI) :
    BlowupDensity.T19.ProjectionAPI where
  extendedProductDensity := by
    intro ν hν T hT s hs a ha g hg r hr
    obtain ⟨f, hmem, hdist⟩ :=
      h.extendedProductDensity ν hν T hT s hs a ha g hg r hr
    exact ⟨f, by rwa [extendedBreakdownSetT_eq], hdist⟩
  projectionOntoInitialData := by
    intro ν hν T hT
    rw [extendedBreakdownSetT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.initialClassT_eq]
    exact h.projectionOntoInitialData ν hν T hT
  zeroInitialProjection := by
    intro ν hν T hT
    rw [extendedBreakdownSetT_eq]
    exact h.zeroInitialProjection ν hν T hT

/-! ### Round trips and the four headline statement definitions -/

theorem periodic_roundTrip_spec (h : BlowupDensity.T19.PeriodicDensityAPI) :
    periodicOfCanonical (periodicToCanonical h) = h := Subsingleton.elim _ _

theorem periodic_roundTrip_canonical
    (h : NSFormalization.Section3.T19.PeriodicDensityAPI) :
    periodicToCanonical (periodicOfCanonical h) = h := Subsingleton.elim _ _

theorem mixed_roundTrip_spec (h : BlowupDensity.T19.MixedRegionAPI) :
    mixedOfCanonical (mixedToCanonical h) = h := Subsingleton.elim _ _

theorem mixed_roundTrip_canonical
    (h : NSFormalization.Section3.T19.MixedRegionAPI) :
    mixedToCanonical (mixedOfCanonical h) = h := Subsingleton.elim _ _

theorem strong_roundTrip_spec (h : BlowupDensity.T19.StrongClosureAPI) :
    strongOfCanonical (strongToCanonical h) = h := Subsingleton.elim _ _

theorem strong_roundTrip_canonical
    (h : NSFormalization.Section3.T19.StrongClosureAPI) :
    strongToCanonical (strongOfCanonical h) = h := Subsingleton.elim _ _

theorem projection_roundTrip_spec (h : BlowupDensity.T19.ProjectionAPI) :
    projectionOfCanonical (projectionToCanonical h) = h := Subsingleton.elim _ _

theorem projection_roundTrip_canonical
    (h : NSFormalization.Section3.T19.ProjectionAPI) :
    projectionToCanonical (projectionOfCanonical h) = h := Subsingleton.elim _ _

theorem regularTrajectoryT_eq :
    @BlowupDensity.T19.RegularTrajectoryT =
      @NSFormalization.Section3.T19.RegularTrajectoryT := by
  funext ν a T u
  exact propext (regularTrajectoryT_iff ν a T u)

theorem singularTrajectoryT_eq :
    @BlowupDensity.T19.SingularTrajectoryT =
      @NSFormalization.Section3.T19.SingularTrajectoryT := by
  funext ν a T u
  exact propext (singularTrajectoryT_iff ν a T u)

theorem periodicDensityStatement_eq :
    BlowupDensity.T19.periodicDensityStatement =
      NSFormalization.Section3.T19.periodicDensityStatement := by
  apply propext
  constructor
  · intro h a ha ν hν T hT s hs
    have hd := h a ha ν hν T hT s hs
    rw [BlowupDensity.Bindings.TorusLocalTheory.relativelyDenseT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq] at hd
    exact hd
  · intro h a ha ν hν T hT s hs
    rw [BlowupDensity.Bindings.TorusLocalTheory.relativelyDenseT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq]
    exact h a ha ν hν T hT s hs

theorem mixedRegionStatement_eq :
    BlowupDensity.T19.mixedRegionStatement =
      NSFormalization.Section3.T19.mixedRegionStatement := by
  apply propext
  constructor
  · intro h a ha ν hν T hT p q _ hq hregion
    have hd := h a ha ν hν T hT p q hq hregion
    rw [relativelyDenseMixedT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq] at hd
    exact hd
  · intro h a ha ν hν T hT p q _ hq hregion
    rw [relativelyDenseMixedT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq,
      BlowupDensity.Bindings.TorusLocalTheory.breakdownSetT_eq]
    exact h a ha ν hν T hT p q hq hregion

theorem strongClosureStatement_eq :
    BlowupDensity.T19.strongClosureStatement =
      NSFormalization.Section3.T19.strongClosureStatement := by
  apply propext
  constructor
  · intro h a ha ν hν T hT u hregular r hr
    obtain ⟨u', hsingular, hdist⟩ :=
      h a ha ν hν T hT u ((regularTrajectoryT_iff ν a T u).mpr hregular) r hr
    exact ⟨u', (singularTrajectoryT_iff ν a T u').mp hsingular, hdist⟩
  · intro h a ha ν hν T hT u hregular r hr
    obtain ⟨u', hsingular, hdist⟩ :=
      h a ha ν hν T hT u ((regularTrajectoryT_iff ν a T u).mp hregular) r hr
    exact ⟨u', (singularTrajectoryT_iff ν a T u').mpr hsingular, hdist⟩

theorem projectionStatement_eq :
    BlowupDensity.T19.projectionStatement =
      NSFormalization.Section3.T19.projectionStatement := by
  apply propext
  constructor
  · intro h ν hν T hT
    refine ⟨?_, ?_⟩
    · intro s hs a ha g hg r hr
      obtain ⟨f, hmem, hdist⟩ := h ν hν T hT |>.1 s hs a ha g hg r hr
      exact ⟨f, by rwa [extendedBreakdownSetT_eq] at hmem, hdist⟩
    · simpa only [extendedBreakdownSetT_eq,
        BlowupDensity.Bindings.TorusLocalTheory.initialClassT_eq] using
        (h ν hν T hT).2
  · intro h ν hν T hT
    refine ⟨?_, ?_⟩
    · intro s hs a ha g hg r hr
      obtain ⟨f, hmem, hdist⟩ := h ν hν T hT |>.1 s hs a ha g hg r hr
      exact ⟨f, by rwa [extendedBreakdownSetT_eq], hdist⟩
    · rw [extendedBreakdownSetT_eq,
        BlowupDensity.Bindings.TorusLocalTheory.initialClassT_eq]
      exact (h ν hν T hT).2

end T19CanonicalProbe

#print axioms T19CanonicalProbe.criticalOrder_eq
#print axioms T19CanonicalProbe.alpha_eq
#print axioms T19CanonicalProbe.periodicTorusMeasure_eq
#print axioms T19CanonicalProbe.torusLift_eq
#print axioms T19CanonicalProbe.initialClassT_eq
#print axioms T19CanonicalProbe.forceClassT_eq
#print axioms T19CanonicalProbe.forceSobolevENormT_eq
#print axioms T19CanonicalProbe.relativelyDenseT_eq
#print axioms T19CanonicalProbe.energyEssSupT_eq
#print axioms T19CanonicalProbe.energyENormT_eq
#print axioms T19CanonicalProbe.mixedSlicePath_eq
#print axioms T19CanonicalProbe.mixedLebesgueENormT_eq
#print axioms T19CanonicalProbe.spaceTimeL2L2ENormT_eq
#print axioms T19CanonicalProbe.relativelyDenseMixedT_eq
#print axioms T19CanonicalProbe.limsupLeft_eq
#print axioms T19CanonicalProbe.speedENorm_eq
#print axioms T19CanonicalProbe.maximalLifespanT_eq
#print axioms T19CanonicalProbe.regularThroughT_eq
#print axioms T19CanonicalProbe.breakdownSetT_eq
#print axioms T19CanonicalProbe.regularTrajectoryT_iff
#print axioms T19CanonicalProbe.singularTrajectoryT_iff
#print axioms T19CanonicalProbe.extendedBreakdownSetT_eq
#print axioms T19CanonicalProbe.periodicToCanonical
#print axioms T19CanonicalProbe.periodicOfCanonical
#print axioms T19CanonicalProbe.mixedToCanonical
#print axioms T19CanonicalProbe.mixedOfCanonical
#print axioms T19CanonicalProbe.strongToCanonical
#print axioms T19CanonicalProbe.strongOfCanonical
#print axioms T19CanonicalProbe.projectionToCanonical
#print axioms T19CanonicalProbe.projectionOfCanonical
#print axioms T19CanonicalProbe.periodic_roundTrip_spec
#print axioms T19CanonicalProbe.periodic_roundTrip_canonical
#print axioms T19CanonicalProbe.mixed_roundTrip_spec
#print axioms T19CanonicalProbe.mixed_roundTrip_canonical
#print axioms T19CanonicalProbe.strong_roundTrip_spec
#print axioms T19CanonicalProbe.strong_roundTrip_canonical
#print axioms T19CanonicalProbe.projection_roundTrip_spec
#print axioms T19CanonicalProbe.projection_roundTrip_canonical
#print axioms T19CanonicalProbe.regularTrajectoryT_eq
#print axioms T19CanonicalProbe.singularTrajectoryT_eq
#print axioms T19CanonicalProbe.periodicDensityStatement_eq
#print axioms T19CanonicalProbe.mixedRegionStatement_eq
#print axioms T19CanonicalProbe.strongClosureStatement_eq
#print axioms T19CanonicalProbe.projectionStatement_eq
