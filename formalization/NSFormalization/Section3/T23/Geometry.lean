import NSFormalization.Section3.T23.Placement

/-! Auxiliary geometry for the prescribed interior ball, with openness explicit. -/
namespace NSFormalization.Section3.T23
open Set
open NavierStokes.ProblemStatement

/-- The prescribed closed ball is compact in physical space. -/
theorem prescribed_closedBall_compact (c : Space) (R : ℝ) :
    IsCompact (Metric.closedBall c R) := isCompact_closedBall c R

/-- Every permitted insertion center has a positive closed ball inside the prescribed ball. -/
theorem exists_inner_closedBall {c x₀ : Space} {R : ℝ}
    (hx : x₀ ∈ Metric.ball c R) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x₀ r ⊆ Metric.ball c R := by
  refine ⟨(R - dist x₀ c) / 2, by have := Metric.mem_ball.mp hx; linarith, ?_⟩
  intro y hy
  have hy' := Metric.mem_closedBall.mp hy
  have hx' := Metric.mem_ball.mp hx
  have htri := dist_triangle y x₀ c
  exact Metric.mem_ball.mpr (by linarith)

/-- An interior closed ball misses the frontier of an open domain. -/
theorem prescribed_closedBall_disjoint_frontier {Ω : Set Space} (hΩ : IsOpen Ω)
    {c : Space} {R : ℝ} (hball : Metric.closedBall c R ⊆ Ω) :
    Disjoint (Metric.closedBall c R) (frontier Ω) := by
  apply Set.disjoint_left.mpr
  intro x hx hfront
  exact hfront.2 (by simpa only [hΩ.interior_eq] using hball hx)

end NSFormalization.Section3.T23
