import NSFormalization.Section3.T13.Assembly
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal Topology
namespace NSFormalization.Section3.T13
example : ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ), 0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube → ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) → periodicSobolevENorm s (periodize f) ≤ 0 := by
  intro s hs hs1 c r hr hb
  exact localization s hs hs1 c r hr hb
end NSFormalization.Section3.T13
