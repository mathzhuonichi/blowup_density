import NSFormalization.Section3.T18.Support

open Set
open NSFormalization.Section3.T18

/-- The quantified scale and time domains in U7 are simultaneously inhabited. -/
example (data : InsertionData) :
    ∃ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∃ t ∈ Ico (0 : ℝ) data.place.T, True := by
  refine ⟨ε₀ data, ⟨eps_pos data, le_rfl⟩, 0, ⟨le_rfl, data.place.time_pos⟩, trivial⟩
