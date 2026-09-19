import NSFormalization.Section3.T18.Kinematics
namespace NSFormalization.Section3.T18
open Set
open NavierStokes.ProblemStatement
example (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t : ℝ, 0 ≤ t → t ≤ data.place.T - 3 * ε ^ 2 → ∀ x : Space,
      velocity data ε (t, x) = data.reference.velocity (t, x) := by
  intro ε hε t ht0 ht x
  exact history data ε hε t ht0 (by linarith)
end NSFormalization.Section3.T18
