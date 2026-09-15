import NSFormalization.Section4.D01.HomogeneousNorm

noncomputable section

open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

namespace NSFormalization.Section4.D01

open Homogeneous (SpatialField IsHomogeneousSliceDatum)

/-- Premise-free witness that the datum infimum is inhabited for the zero field. -/
example (s : ℝ) :
    ∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s (0 : SpatialField) G := by
  refine ⟨0, 0, ?_, ?_⟩
  · simp [Homogeneous.IsSliceDistribution]
  · simp [Homogeneous.IsHomogeneousVectorDatum, Homogeneous.IsHomogeneousDatum]

/-- The substantive `0 ↦ 1` mutation of the zero theorem is false. -/
example (s : ℝ) :
    dotHomogeneousENorm s (0 : SpatialField) ≠ (1 : ℝ≥0∞) := by
  simp

end NSFormalization.Section4.D01
