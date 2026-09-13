import Bindings.HomogeneousPartialV2

noncomputable section
namespace BlowupDensity.Tests

open Set MeasureTheory
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

def checkedHomogeneousPartialV2 :
    Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API :=
  Bindings.homogeneousPartialV2

-- numeric side goals
example : (1 : ℝ≥0∞) ≤ 2 := one_le_two
example : (2 : ℝ≥0∞) ≠ ⊤ := (by simp)
example : Contracts.V1.HomogeneousPartial.SplitRange (-1 : ℝ) := ⟨by norm_num, by norm_num⟩

-- Example A: density conclusion (04-whole-space.tex:219,228), q=2, s=-1, unfolded ∃ form
example : ∀ b : ℝ → RealVectorSobolev (-1 : ℝ),
    MemBochnerDatum 2 (-1) b → ∀ r : ℝ≥0∞, 0 < r →
      ∃ f ∈ forceClassCompact, ∃ D : ℝ → RealVectorSobolev (-1 : ℝ),
        IsHomogeneousPath (-1) f D ∧
          AEStronglyMeasurable D forceTimeMeasure ∧
          bochnerDatumENorm 2 (-1) (D - b) < r :=
  checkedHomogeneousPartialV2.approxCompactHomogeneous 2 one_le_two (by simp) (-1)
    ⟨by norm_num, by norm_num⟩

-- Example B: separated-sum membership in F_c (04-whole-space.tex:260)
example (s : ℝ) (hs : -3 / 2 < s) (J : ℕ) (φ : Fin J → ℝ → ℝ)
    (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s)
    (hφs : ∀ j, ContDiff ℝ ∞ (φ j)) (hφc : ∀ j, HasCompactSupport (φ j))
    (hφpos : ∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ))
    (hhs : ∀ j, ContDiff ℝ ∞ (h j)) (hhc : ∀ j, HasCompactSupport (h j))
    (hA : ∀ j, IsHomogeneousSliceDatum s (h j) (A j)) :
    Contracts.V1.BochnerPartial.separatedField φ h ∈ forceClassCompact ∧
      IsHomogeneousPath s (Contracts.V1.BochnerPartial.separatedField φ h)
        (Contracts.V1.BochnerPartial.separatedPath φ A) :=
  have H := checkedHomogeneousPartialV2.separatedAssembly s hs J φ h A
    hφs hφc hφpos hhs hhc hA
  ⟨H.1, H.2.1⟩

end BlowupDensity.Tests
