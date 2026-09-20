import Tests.CompletedDensity

/-! Transitive axiom and public-API conformance audit for R46 V1. -/

open Set Filter
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal Topology

#print axioms NSFormalization.Section4.I03.compactHomogeneousRealization
#print axioms BlowupDensity.Bindings.completedSobolevDensity
#print axioms BlowupDensity.Bindings.completedHomogeneousDensity_of_realization
#print axioms BlowupDensity.Bindings.strongTrajectoryClosure_of_realization
#print axioms BlowupDensity.Bindings.completedDensity
#print axioms BlowupDensity.Tests.checkedCompletedDensity

/-- The registered inhomogeneous abbreviation has the Spec's exact expansion. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S =
      CompletedDenseVia q s (IsSobolevPath s) S := rfl

/-- The registered homogeneous abbreviation has the Spec's exact expansion. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl

/-- The checked witness conforms to the complete registered API. -/
theorem completedDensityContractConformance :
    BlowupDensity.Contracts.V1.CompletedDensity.CompletedDensityAPI :=
  BlowupDensity.Tests.checkedCompletedDensity

#print axioms completedDensityContractConformance
