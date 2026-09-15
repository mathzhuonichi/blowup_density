import NSFormalization.Section4.D01.HomogeneousNorm

noncomputable section

open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

namespace NSFormalization.Section4.D01

open Homogeneous (SpatialField IsHomogeneousSliceDatum)

/-- Deliberately false mutation of `dotHomogeneousENorm_zero`: `0` is changed to `1`. -/
example (s : ℝ) :
    dotHomogeneousENorm s (0 : SpatialField) = (1 : ℝ≥0∞) := by
  have hzero : IsHomogeneousSliceDatum s (0 : SpatialField) 0 := by
    refine ⟨0, ?_, ?_⟩
    · simp [Homogeneous.IsSliceDistribution]
    · simp [Homogeneous.IsHomogeneousVectorDatum, Homogeneous.IsHomogeneousDatum]
  exact le_antisymm
    ((dotHomogeneousENorm_le_of_isHomogeneousSlice hzero).trans (by simp)) bot_le

end NSFormalization.Section4.D01
