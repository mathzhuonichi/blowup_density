import NSFormalization.Section3.T24.AffineMomentum
noncomputable section
namespace NSFormalization.Section3.T24
open Set NavierStokes.ProblemStatement
open scoped ContDiff
def badForce (ν : ℝ) (U F b : VelocityField) : VelocityField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 - ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 - crossAdvection b b z.1 z.2
example (ν : ℝ) (U F b : VelocityField) : affineForce ν U F b ≠ badForce ν U F b := by
  intro h
  have hz := congrFun h (0, 0)
  simp [affineForce, badForce] at hz
end NSFormalization.Section3.T24
