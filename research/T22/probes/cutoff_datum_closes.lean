import NSFormalization.Section3.T22.Domain

namespace NSFormalization.Section3.T22
open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)

example : IsOpen (ball (0 : Space) 1) := isOpen_ball
example : IsCompact (closedBall (0 : Space) (1 / 2)) := isCompact_closedBall

end NSFormalization.Section3.T22
