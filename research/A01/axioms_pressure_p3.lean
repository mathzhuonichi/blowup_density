import NSFormalization.Section4.A01.ConstructorPressure

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open Set
open scoped ContDiff

#print axioms momentumResidualOfVelocity
#print axioms pressureGradientOfVelocity
#print axioms pressureOfVelocity
#print axioms pressureOfVelocity_basepoint
#print axioms pressureGradientOfVelocity_memLp
#print axioms pressureGradient_pressureOfVelocity
#print axioms pressureGradient_pressureOfVelocity_lerayComplement
#print axioms pressureGradient_pressureOfVelocity_lerayComplement_order
#print axioms pressure_gradient_memLp_slice
#print axioms pressure_gradient_memLp
#print axioms pressureOfVelocity_slice_smooth
#print axioms pressure_smooth_of_velocity_smooth
#print axioms momentum_of_projected
#print axioms pressureOfVelocity_zero

/-- Signature conformance after review N1: momentum needs smoothness and
curl-freeness of the explicit gradient, with no redundant pointwise projected
equation hypothesis. -/
example {T : ℝ} (ν : ℝ) (f velocity : VelocityField)
    (hvelocity : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0)
    (hgradient_smooth : ∀ t ∈ Ioo (0 : ℝ) T,
      ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hgradient_symm : ∀ t ∈ Ioo (0 : ℝ) T,
      RadialPotential.HasSymmetricJacobian
        (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual
        ν velocity (pressureOfVelocity ν f velocity) t x = f (t, x) :=
  momentum_of_projected ν f velocity hvelocity hdiv hgradient_smooth hgradient_symm

/-- The constructor is inhabited and its fixed gauge is concrete: zero velocity
and zero force give the zero pressure, for every viscosity. -/
example (ν : ℝ) :
    pressureOfVelocity ν (0 : VelocityField) (0 : VelocityField) = 0 :=
  pressureOfVelocity_zero ν
