import NSFormalization.Section3.T18.Momentum

noncomputable section
namespace NSFormalization.Section3.T18.Rev433

open Set

-- Conditional non-vacuity check: the threaded correction threshold makes the
-- scale interval used by U5/U6 nonempty.
example (data : InsertionData) : ∃ ε : ℝ, ε ∈ Ioc (0 : ℝ) (ε₀ data) := by
  refine ⟨ε₀ data, ?_⟩
  exact ⟨eps_pos data, le_rfl⟩

end NSFormalization.Section3.T18.Rev433
