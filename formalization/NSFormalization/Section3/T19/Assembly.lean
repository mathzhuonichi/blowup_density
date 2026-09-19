import NSFormalization.Section3.T19.Closure
import NSFormalization.Section3.T19.Projection

/-!
# T19 assembly: the periodic density package

The thirteen fields below are the proved U1--U14 theorems.  The four
statement theorems expose the headline propositions of `prop:density`,
`cor:mixed`, `cor:closure`, and `prop:projection`.
-/

noncomputable section

namespace NSFormalization.Section3.T19
set_option linter.defProp false

/-- The complete three-field canonical package for `prop:density`. -/
def periodicDensityAPI : PeriodicDensityAPI where
  fixedInitialDensity := fixedInitialDensity
  thresholdValue := thresholdValue
  regularReferenceSingular := regularReferenceSingular

/-- The complete three-field canonical package for `cor:mixed`. -/
def mixedRegionAPI : MixedRegionAPI where
  mixedDensity := mixedDensity
  mixedRegionArithmetic := mixedRegionArithmetic
  regionExamples := regionExamples

/-- The complete four-field canonical package for `cor:closure`. -/
def strongClosureAPI : StrongClosureAPI where
  energyTimeEmbedding := energyTimeEmbedding
  closureInEnergy := closureInEnergy
  simultaneousPairConvergence := simultaneousPairConvergence
  referenceFiniteEnergy := referenceFiniteEnergy

/-- The complete three-field canonical package for `prop:projection`. -/
def projectionAPI : ProjectionAPI where
  extendedProductDensity := extendedProductDensity
  projectionOntoInitialData := projectionOntoInitialData
  zeroInitialProjection := zeroInitialProjection

/-- `prop:density`, closed in the canonical Section 3 vocabulary. -/
theorem periodicDensityStatement_holds : periodicDensityStatement :=
  periodicDensityAPI.fixedInitialDensity

/-- `cor:mixed`, closed in the canonical Section 3 vocabulary. -/
theorem mixedRegionStatement_holds : mixedRegionStatement :=
  mixedRegionAPI.mixedDensity

/-- `cor:closure`, closed in the canonical Section 3 vocabulary. -/
theorem strongClosureStatement_holds : strongClosureStatement :=
  strongClosureAPI.closureInEnergy

/-- `prop:projection`, closed in the canonical Section 3 vocabulary. -/
theorem projectionStatement_holds : projectionStatement := by
  intro nu hnu T hT
  exact ⟨projectionAPI.extendedProductDensity nu hnu T hT,
    projectionAPI.projectionOntoInitialData nu hnu T hT⟩

end NSFormalization.Section3.T19
