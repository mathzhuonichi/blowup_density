import NSFormalization.Section3.T24.MultipleAssembled

noncomputable section
namespace NSFormalization.Section3.T24.Rev468Nonvacuity

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10

variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData ν u p f K M E)

/-- The assembled theorem is not hidden behind an empty region family or an
empty interior-time interval. -/
theorem index_and_interior_time_nonempty :
    Nonempty (Fin d.N) ∧ ∃ t : ℝ, t ∈ Ioo (0 : ℝ) d.T := by
  constructor
  · exact ⟨⟨0, d.N_pos⟩⟩
  · refine ⟨d.T / 2, ?_⟩
    constructor <;> linarith [d.hT]

end NSFormalization.Section3.T24.Rev468Nonvacuity
