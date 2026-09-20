import NSFormalization.Section3.T15.Bridges

noncomputable section

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15

def reviewerUnitForce : VelocityField :=
  fun _ => coordinateVector (0 : Fin 3)

/- At a concrete nonzero scale, the rescaling of a nonzero constant force is
still nonzero. -/
example : scaledForce reviewerUnitForce (0 : Space) 1 1 (1, 0) ≠ 0 := by
  have hc : coordinateVector (0 : Fin 3) ≠ (0 : Space) := by
    intro h
    have h0 := congrArg (fun v : Space => v 0) h
    simp [coordinateVector] at h0
  simpa [scaledForce, scaledSourcePoint, scaledStartTime, reviewerUnitForce] using hc
