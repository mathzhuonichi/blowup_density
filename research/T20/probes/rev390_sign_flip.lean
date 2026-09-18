import NSFormalization.Section3.T20.ConstantTransport

/-!
Reviewer negative mutation for lane 390.  The main skew-adjointness conclusion
is substantively mutated by flipping its minus sign to a plus sign.  Applying
the lane theorem must fail with a conclusion type mismatch.
-/

noncomputable section

namespace Rev390SignFlip

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open NSFormalization.Section3.T20
open NSFormalization.Section4.A02 (SpatialField)
open scoped InnerProductSpace

example : ∀ (m : Space) (v w : SpatialField),
    SmoothPeriodicT v → SmoothPeriodicT w →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift (constantTransportSpatialT m v) y)
            (torusLift w y) : ℝ)) periodicTorusMeasure →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift v y)
            (torusLift (constantTransportSpatialT m w) y) : ℝ))
        periodicTorusMeasure →
        periodicPairing (constantTransportSpatialT m v) w =
          periodicPairing v (constantTransportSpatialT m w) := by
  exact constantTransportSkew

end Rev390SignFlip
