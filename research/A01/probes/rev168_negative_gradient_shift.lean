import NSFormalization.Section4.A01.ConstructorPressure

noncomputable section

namespace Rev168

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open scoped ContDiff

/-- Negative mutation: adding the nonzero first coordinate vector to the main
gradient conclusion must not be accepted by the original radial-potential
proof. -/
example (ν : ℝ) (f velocity : VelocityField) (t : ℝ)
    (hsmooth : ContDiff ℝ ∞
      (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hsym : RadialPotential.HasSymmetricJacobian
      (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (x : Space) :
    pressureGradient (pressureOfVelocity ν f velocity) t x =
      pressureGradientOfVelocity ν f velocity (t, x) + coordinateVector 0 := by
  exact pressureGradient_pressureOfVelocity ν f velocity t hsmooth hsym x

end Rev168
