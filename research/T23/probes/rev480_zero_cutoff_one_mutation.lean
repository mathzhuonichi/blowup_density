import NSFormalization.Section3.T23.Boundary

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T22 (BoundedDomainNormAPI)

namespace NSFormalization.Section3.T23

-- Reviewer mutation: changing the obstructing cutoff threshold from `0` to `1`
-- must invalidate the proof of `boundaryInsertionAPI_zero_cutoff`.
/--
error: Application type mismatch: The argument
  A.eps_pos
has type
  0 < A.ε₀
but is expected to have type
  1 < A.ε₀
in the application
  not_lt_of_ge hl A.eps_pos
-/
#guard_msgs in
theorem rev480_boundaryInsertionAPI_one_cutoff
    (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (M E : ℝ) (place : DomainPlacementData u p f K)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : CutoffData) (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (hD : D.ε₀ = 1) :
    ¬ Nonempty (BoundaryInsertionAPI ν u p f K M E place Ω norms a g r δ D reference) := by
  rintro ⟨A⟩
  have hl := A.eps_le_cutoff
  rw [hD] at hl
  exact (not_lt_of_ge hl) A.eps_pos

end NSFormalization.Section3.T23
