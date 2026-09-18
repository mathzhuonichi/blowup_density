import NSFormalization.Section3.T13.LocalizationKernel

open Set Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)

namespace NSFormalization.Section3.T13

/- A substantive mutation of the geometric conclusion: replacing `2 * r < 1`
   by the false stronger `3 * r < 1` must not be discharged by the shipped
   theorem.  This file is intentionally expected to fail. -/
example {c : Space} {r : ℝ} (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) : 3 * r < 1 := by
  exact two_r_lt_one_of_closure_ball_subset hr hball

end NSFormalization.Section3.T13
