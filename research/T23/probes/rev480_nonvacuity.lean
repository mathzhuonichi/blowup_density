import NSFormalization.Section3.T23.Boundary
import NSFormalization.Section3.T13.ConstantEndpoints

noncomputable section
namespace NSFormalization.Section3.T23.ReviewerProbe

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T13

def reviewBox : Set Space :=
  {x : Space | ∀ i : Fin 3, (-2 : ℝ) < x i ∧ x i < 2}

theorem reviewBox_shape : IsBoxDomain reviewBox := by
  exact ⟨fun _ => -2, fun _ => 2, by intro i; norm_num, rfl⟩

theorem reviewBox_class : IsBoundedBoxOrSmoothDomain reviewBox := by
  refine ⟨reviewBox_shape.open_bounded.1, reviewBox_shape.open_bounded.2, ?_, Or.inl reviewBox_shape⟩
  exact ⟨0, by intro i; norm_num⟩

theorem closed_unitBall_in_reviewBox :
    closure (Metric.ball (0 : Space) 1) ⊆ reviewBox := by
  intro x hx i
  have hn : ‖x‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (Metric.closure_ball_subset_closedBall hx)
  have hc : |x i| ≤ ‖x‖ := abs_spaceCoord_le_norm x i
  exact abs_lt.mp (lt_of_le_of_lt (hc.trans hn) (by norm_num))

def reviewVelocity : VelocityField := 0
def reviewPressure : PressureField := 0
def reviewForce : VelocityField := 0
def reviewCarrier : Set Space := Metric.closedBall (0 : Space) 1

def reviewPlacement :
    DomainPlacementData reviewVelocity reviewPressure reviewForce reviewCarrier :=
  domainPlacementData (isCompact_closedBall (0 : Space) 1) HasCompactSupport.zero
    (0 : Space) 1 (by norm_num) closed_unitBall_in_reviewBox
    (0 : Space) (Metric.mem_ball_self (by norm_num)) 1 (by norm_num)

theorem inner_halfBall_in_chart :
    closure (Metric.ball reviewPlacement.x₀ (1 / 2 : ℝ)) ⊆
      Metric.ball reviewPlacement.chartCenter reviewPlacement.chartRadius := by
  intro x hx
  have hn : dist x (0 : Space) ≤ 1 / 2 :=
    Metric.closure_ball_subset_closedBall hx
  exact Metric.mem_ball.mpr (by
    change dist x (0 : Space) < 1
    linarith)

/-- The canonical placement and every geometric premise added by the G0 repair
are jointly inhabited on a genuine bounded box. -/
example :
    Nonempty (DomainPlacementData reviewVelocity reviewPressure reviewForce reviewCarrier) ∧
    IsBoundedBoxOrSmoothDomain reviewBox ∧
    0 < (1 / 2 : ℝ) ∧
    closure (Metric.ball reviewPlacement.x₀ (1 / 2 : ℝ)) ⊆
      Metric.ball reviewPlacement.chartCenter reviewPlacement.chartRadius ∧
    closure (Metric.ball reviewPlacement.chartCenter reviewPlacement.chartRadius) ⊆ reviewBox := by
  exact ⟨⟨reviewPlacement⟩, reviewBox_class, by norm_num,
    inner_halfBall_in_chart, closed_unitBall_in_reviewBox⟩

end NSFormalization.Section3.T23.ReviewerProbe
