import NSFormalization.Section3.T13.KernelComparison
open Set MeasureTheory
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff
open NavierStokes.ProblemStatement
open scoped ENNReal
-- Mutation: replace the proved factor 4 by 5; the theorem no longer applies.
example {s : ℝ} {c : Space} {r : ℝ} {f : SpatialField}
    (hs : 0 < s) (hs1 : s < 1) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hf : ContDiff ℝ ∞ f) (hsupp : SupportedInBall c r f) :
    ITorus s (periodize f) ≤ IReal s f + 5 * tailGeomConst s c r * (eLpNorm f 2 volume) ^ 2 := by
  exact iTorus_periodize_le hs hs1 hr hball hf hsupp
