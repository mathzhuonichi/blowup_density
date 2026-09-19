import NSFormalization.Section3.T23.Solution

namespace NSFormalization.Section3.T23.InsertedTriple

open Set
open NavierStokes.ProblemStatement

/-- The common threshold has an actual admissible positive scale. -/
example {u f : VelocityField} {p : PressureField} {K : Set Space}
    (place : DomainPlacementData u p f K) (D : CutoffData) (s b : ℝ)
    (hD : 0 < D.ε₀) (hs : 0 < s) (hb : 0 < b) :
    ∃ ε : ℝ, ε ∈ Ioc 0 (threshold place D s b) := by
  have he : 0 < threshold place D s b := eps_pos place D hD hs hb
  refine ⟨threshold place D s b / 2, ?_⟩
  constructor <;> linarith

end NSFormalization.Section3.T23.InsertedTriple
