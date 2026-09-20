import NSFormalization.Section3.T22.ZeroExtensionComparison
open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section3.T22
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal Topology
-- substantive mutation: reverse the left inequality
example : ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
      ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
        ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
        sobolevENorm s (zeroExtension Ω z) ≤ domainSobolevENorm Ω s (restrictField Ω z) := by
  exact zeroExtensionComparison
