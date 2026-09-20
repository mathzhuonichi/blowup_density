import NSFormalization.Section4.R44.TrilinearJ

open NavierStokes.ProblemStatement
open NSFormalization.Section4.R44

/-!
Reviewer mutation probe: reversing the sign of the main estimate's positive
constant must not be accepted by the proof of `advection_pairing_le`.
-/

example {u f : Space → Space}
    (h : JWeightDatum u f) (ha : AdvectionJDatum h) :
    |advectionJPairing h ha| ≤
      -trilinearConstJ * Y u * (Y u ^ 2 + Z u ^ 2) := by
  exact advection_pairing_le h ha
