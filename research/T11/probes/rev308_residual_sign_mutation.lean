import NSFormalization.Section3.T11.FlowConversion

noncomputable section

namespace NSFormalization.Section3.T11.ReviewerProbe

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T11

/- This is intentionally false as a use of the reviewed bridge: the left-hand
side has viscosity `-ν`, while the right-hand side and supplied theorem use
`ν`.  The reviewer expects elaboration to reject the proof term. -/
example (ν : ℝ) (u : SpaceTimeField) (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    Source.residual (-ν) u p t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x :=
  source_residual_eq_navierStokesResidual ν u p t x

end NSFormalization.Section3.T11.ReviewerProbe
