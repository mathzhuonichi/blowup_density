import Contracts.V1.Density
import NSFormalization.Section3.T19.Assembly
import Bindings.TorusLocalTheory
import Bindings.Scaling3
import Bindings.MaximalPartial

/-!
# Binding for the T19 periodic density contract

Registered definitions are guarded by `rfl`.  The only inductive mismatch is
the separately restated `ClassicalSolutionT`; trajectory witnesses therefore
move through `Bindings.TorusLocalTheory.toContract` and `ofContract` field by
field.  Every occurrence of maximal lifespan is transported through
`Bindings.TorusLocalTheory.maximalLifespanT_eq`.
-/

noncomputable section

namespace BlowupDensity.Bindings.Density

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.Density
open scoped ENNReal Topology BigOperators

/-! ## Definitional drift guards -/

theorem criticalOrder_eq :
    BlowupDensity.Contracts.V1.Data.criticalOrder =
      NSFormalization.Section3.T19.criticalOrder := rfl

theorem mixedLebesgueENormT_eq :
    @BlowupDensity.Contracts.V1.Scaling3.mixedLebesgueENormT =
      @NSFormalization.Section3.T19.mixedLebesgueENormT := rfl

theorem spaceTimeL2L2ENormT_eq :
    BlowupDensity.Contracts.V1.Density.spaceTimeL2L2ENormT =
      NSFormalization.Section3.T19.spaceTimeL2L2ENormT := rfl

theorem relativelyDenseMixedT_eq :
    @BlowupDensity.Contracts.V1.Density.RelativelyDenseMixedT =
      @NSFormalization.Section3.T19.RelativelyDenseMixedT := rfl

/-! ## Structure-exception transports -/

theorem regularTrajectory_toCanonical {ν T : ℝ} {a : SpatialField}
    {u : SpaceTimeField} (h : RegularTrajectoryT ν a T u) :
    NSFormalization.Section3.T19.RegularTrajectoryT ν a T u := by
  obtain ⟨g, hg, δ, hδ, w, hw⟩ := h
  exact ⟨g, hg, δ, hδ, TorusLocalTheory.ofContract w, hw⟩

theorem regularTrajectory_toContract {ν T : ℝ} {a : SpatialField}
    {u : SpaceTimeField}
    (h : NSFormalization.Section3.T19.RegularTrajectoryT ν a T u) :
    RegularTrajectoryT ν a T u := by
  obtain ⟨g, hg, δ, hδ, w, hw⟩ := h
  exact ⟨g, hg, δ, hδ, TorusLocalTheory.toContract w, hw⟩

theorem singularTrajectory_toCanonical {ν T : ℝ} {a : SpatialField}
    {u : SpaceTimeField} (h : SingularTrajectoryT ν a T u) :
    NSFormalization.Section3.T19.SingularTrajectoryT ν a T u := by
  obtain ⟨g, hg, ⟨w, hw⟩, hfinite, hblowup⟩ := h
  exact ⟨g, hg, ⟨TorusLocalTheory.ofContract w, hw⟩, hfinite, hblowup⟩

theorem singularTrajectory_toContract {ν T : ℝ} {a : SpatialField}
    {u : SpaceTimeField}
    (h : NSFormalization.Section3.T19.SingularTrajectoryT ν a T u) :
    SingularTrajectoryT ν a T u := by
  obtain ⟨g, hg, ⟨w, hw⟩, hfinite, hblowup⟩ := h
  exact ⟨g, hg, ⟨TorusLocalTheory.toContract w, hw⟩, hfinite, hblowup⟩

theorem extendedBreakdownSetT_eq (ν T : ℝ) :
    BlowupDensity.Contracts.V1.Density.extendedBreakdownSetT ν T =
      NSFormalization.Section3.T19.extendedBreakdownSetT ν T := by
  ext p
  constructor
  · rintro ⟨ha, hf, hlife⟩
    refine ⟨ha, hf, ?_⟩
    rwa [← TorusLocalTheory.maximalLifespanT_eq]
  · rintro ⟨ha, hf, hlife⟩
    refine ⟨ha, hf, ?_⟩
    rwa [TorusLocalTheory.maximalLifespanT_eq]

/-! ## The four complete records -/

/-- The canonical three-field density record in registered spelling. -/
theorem periodicDensityAPI : PeriodicDensityAPI where
  fixedInitialDensity := by
    intro a ha ν hν T hT s hs
    rw [TorusLocalTheory.relativelyDenseT_eq,
      TorusLocalTheory.breakdownSetT_eq]
    exact NSFormalization.Section3.T19.periodicDensityAPI.fixedInitialDensity
      a ha ν hν T hT s hs
  thresholdValue := NSFormalization.Section3.T19.periodicDensityAPI.thresholdValue
  regularReferenceSingular := by
    intro a ha ν hν T hT g hg hreg s hs r hr
    have hreg' : NSFormalization.Section3.T10.RegularThroughT ν a g T := by
      rwa [← TorusLocalTheory.regularThroughT_eq]
    obtain ⟨f, hf, hdist, hlife⟩ :=
      NSFormalization.Section3.T19.periodicDensityAPI.regularReferenceSingular
        a ha ν hν T hT g hg hreg' s hs r hr
    refine ⟨f, hf, hdist, ?_⟩
    rwa [TorusLocalTheory.maximalLifespanT_eq]

/-- The canonical three-field mixed-region record in registered spelling. -/
theorem mixedRegionAPI : MixedRegionAPI where
  mixedDensity := by
    intro a ha ν hν T hT p q hp hq hpq g hg r hr
    obtain ⟨f, ⟨hf, hlife⟩, hdist⟩ :=
      NSFormalization.Section3.T19.mixedRegionAPI.mixedDensity
        a ha ν hν T hT p q hq hpq g hg r hr
    refine ⟨f, ⟨hf, ?_⟩, hdist⟩
    rwa [TorusLocalTheory.maximalLifespanT_eq]
  mixedRegionArithmetic :=
    NSFormalization.Section3.T19.mixedRegionAPI.mixedRegionArithmetic
  regionExamples := NSFormalization.Section3.T19.mixedRegionAPI.regionExamples

/-- The canonical four-field strong-closure record in registered spelling. -/
theorem strongClosureAPI : StrongClosureAPI where
  energyTimeEmbedding :=
    NSFormalization.Section3.T19.strongClosureAPI.energyTimeEmbedding
  closureInEnergy := by
    intro a ha ν hν T hT u hregular r hr
    obtain ⟨u', hsingular, hdist⟩ :=
      NSFormalization.Section3.T19.strongClosureAPI.closureInEnergy
        a ha ν hν T hT u (regularTrajectory_toCanonical hregular) r hr
    exact ⟨u', singularTrajectory_toContract hsingular, hdist⟩
  simultaneousPairConvergence := by
    intro a ha ν hν T hT g hg δ hδ reference
    obtain ⟨ε₀, hε₀, u, f, hfamily, henergy, hforce⟩ :=
      NSFormalization.Section3.T19.strongClosureAPI.simultaneousPairConvergence
        a ha ν hν T hT g hg δ hδ (TorusLocalTheory.ofContract reference)
    refine ⟨ε₀, hε₀, u, f, ?_, henergy, hforce⟩
    intro ε hε
    obtain ⟨hf, hlife, ⟨w, hw⟩, hsingular⟩ := hfamily ε hε
    refine ⟨hf, ?_, ⟨TorusLocalTheory.toContract w, hw⟩,
      singularTrajectory_toContract hsingular⟩
    rwa [TorusLocalTheory.maximalLifespanT_eq]
  referenceFiniteEnergy := by
    intro a ha ν hν T hT g hg δ hδ reference
    exact NSFormalization.Section3.T19.strongClosureAPI.referenceFiniteEnergy
      a ha ν hν T hT g hg δ hδ (TorusLocalTheory.ofContract reference)

/-- The canonical three-field projection record in registered spelling. -/
theorem projectionAPI : ProjectionAPI where
  extendedProductDensity := by
    intro ν hν T hT s hs a ha g hg r hr
    obtain ⟨f, hmem, hdist⟩ :=
      NSFormalization.Section3.T19.projectionAPI.extendedProductDensity
        ν hν T hT s hs a ha g hg r hr
    refine ⟨f, ?_, hdist⟩
    rwa [extendedBreakdownSetT_eq]
  projectionOntoInitialData := by
    intro ν hν T hT
    rw [extendedBreakdownSetT_eq]
    exact NSFormalization.Section3.T19.projectionAPI.projectionOntoInitialData
      ν hν T hT
  zeroInitialProjection := by
    intro ν hν T hT
    rw [extendedBreakdownSetT_eq]
    exact NSFormalization.Section3.T19.projectionAPI.zeroInitialProjection
      ν hν T hT

/-! ## Headline statements in contract spelling -/

theorem periodicDensityStatement_holds : periodicDensityStatement :=
  periodicDensityAPI.fixedInitialDensity

theorem mixedRegionStatement_holds : mixedRegionStatement :=
  mixedRegionAPI.mixedDensity

theorem strongClosureStatement_holds : strongClosureStatement :=
  strongClosureAPI.closureInEnergy

theorem projectionStatement_holds : projectionStatement := by
  intro ν hν T hT
  exact ⟨projectionAPI.extendedProductDensity ν hν T hT,
    projectionAPI.projectionOntoInitialData ν hν T hT⟩

end BlowupDensity.Bindings.Density
