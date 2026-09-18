import NSFormalization.Section3.T22.ZeroExtRegularity

/-!
Reviewer negative probe: widen the support radius from `1 / 2` to `2` while
keeping the claimed containment in `ball 0 1`.  The original arithmetic proof
must fail at the strict inequality `‖x‖ < 1`; this file is intentionally not a
passing Lean module.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open Set Metric
open NavierStokes.ProblemStatement (Space)

def revΩ : Set Space := ball (0 : Space) 1
def revWidenedK : Set Space := closedBall (0 : Space) (2 : ℝ)

theorem rev408_widened_interval_breaks : revWidenedK ⊆ revΩ := by
  intro x hx
  have hxnorm : ‖x‖ ≤ (2 : ℝ) := by
    simpa [revWidenedK, mem_closedBall, dist_zero_right] using hx
  have hxlt : ‖x‖ < (1 : ℝ) :=
    lt_of_le_of_lt hxnorm (by norm_num)
  simpa [revΩ, mem_ball, dist_zero_right] using hxlt

end NSFormalization.Section3.T22
