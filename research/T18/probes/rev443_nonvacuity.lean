import NSFormalization.Section3.T18.EnergyRate
import NSFormalization.Section3.T18.MixedRate

/-!
# Review 443: non-vacuity probe

The scale interval used by all five U9/U10 conclusions is inhabited for every
canonical `InsertionData`, because its placement/cutoff minimum is positive.
-/

namespace NSFormalization.Section3.T18

open Set

example (data : InsertionData) : ∃ ε : ℝ, ε ∈ Ioc (0 : ℝ) (ε₀ data) := by
  exact ⟨ε₀ data, eps_pos data, le_rfl⟩

end NSFormalization.Section3.T18
