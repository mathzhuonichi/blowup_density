import NSFormalization.Section4.D01.HomogeneousWitness

/-!
# The datum-form spatial homogeneous norm

This module closes gap G1 of `research/R43/COMPARISON.md`: it gives a physical
spatial field the homogeneous norm of its order-`s` datum, and returns `⊤` when
there is no such datum.  This is the homogeneous analogue of
`Section4.D01.sobolevENorm` and is deliberately different from the pointwise
Fourier-integral quantity `homogeneousFourierENorm`.
-/

noncomputable section

namespace NSFormalization.Section4.D01

open NSFormalization.Paper3 (RealVectorSobolev)
open Homogeneous (SpatialField IsHomogeneousSliceDatum)
open scoped ENNReal

/-- `‖z‖_{Ḣ^s}` for a physical spatial field: the infimum of the `L²` norms of
all order-`s` homogeneous data realizing the field.  The empty infimum is `⊤`.

This is token-for-token the definition used by `research/A05/Spec.lean` and
`research/R43/Spec.lean`. -/
def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

/-- Every homogeneous datum is an upper bound for the datum-infimum norm. -/
theorem dotHomogeneousENorm_le_of_isHomogeneousSlice {s : ℝ} {z : SpatialField}
    {G : RealVectorSobolev s} (hG : IsHomogeneousSliceDatum s z G) :
    dotHomogeneousENorm s z ≤ ‖G‖ₑ :=
  iInf_le (fun G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G} => ‖G.1‖ₑ)
    ⟨G, hG⟩

/-- Short consumer spelling for the datum upper bound. -/
theorem le_of_isHomogeneousSlice {s : ℝ} {z : SpatialField}
    {G : RealVectorSobolev s} (hG : IsHomogeneousSliceDatum s z G) :
    dotHomogeneousENorm s z ≤ ‖G‖ₑ :=
  dotHomogeneousENorm_le_of_isHomogeneousSlice hG

/-- The zero physical field has zero homogeneous norm at every real order. -/
@[simp] theorem dotHomogeneousENorm_zero (s : ℝ) :
    dotHomogeneousENorm s (0 : SpatialField) = 0 := by
  have hzero : IsHomogeneousSliceDatum s (0 : SpatialField) 0 := by
    refine ⟨0, ?_, ?_⟩
    · simp [Homogeneous.IsSliceDistribution]
    · simp [Homogeneous.IsHomogeneousVectorDatum, Homogeneous.IsHomogeneousDatum]
  exact le_antisymm
    ((dotHomogeneousENorm_le_of_isHomogeneousSlice hzero).trans (by simp)) bot_le

/-- A supplied homogeneous datum makes the physical-field norm finite. -/
theorem dotHomogeneousENorm_ne_top_of_isHomogeneousSlice {s : ℝ} {z : SpatialField}
    {G : RealVectorSobolev s} (hG : IsHomogeneousSliceDatum s z G) :
    dotHomogeneousENorm s z ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (dotHomogeneousENorm_le_of_isHomogeneousSlice hG)

/-- Existential consumer form: a field with a homogeneous datum has finite norm. -/
theorem dotHomogeneousENorm_ne_top {s : ℝ} {z : SpatialField}
    (hz : ∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s z G) :
    dotHomogeneousENorm s z ≠ ⊤ := by
  obtain ⟨G, hG⟩ := hz
  exact dotHomogeneousENorm_ne_top_of_isHomogeneousSlice hG

end NSFormalization.Section4.D01
