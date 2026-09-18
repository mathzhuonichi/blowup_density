import NSFormalization.Section3.T24.AffineMomentum

/-!
Reviewer negative probe for lane 398.

The main statement's viscous correction is substantively mutated from
`- ν • spatialLaplacian b` to `+ ν • spatialLaplacian b`.  Applying the proved
`momentum` theorem must therefore fail at the force equality.
-/

noncomputable section

namespace Review398

open Set
open NavierStokes.ProblemStatement
open scoped ContDiff
open NSFormalization.Section3.T24

def affineForceWrongViscousSign (ν : ℝ) (U F b : VelocityField) : VelocityField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 + ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 +
    crossAdvection b b z.1 z.2

example {ν : ℝ} {U F : VelocityField} {P : PressureField}
    (c : Space) (r τ₀ τ₁ : ℝ)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hnavier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν U P t x = F (t, x)) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        NavierStokesR3.ProblemStatement.navierStokesResidual ν
            (affineVelocity U b) (affinePressure P) t x =
          affineForceWrongViscousSign ν U F b (t, x) := by
  intro b hb t ht x
  rw [momentum c r τ₀ τ₁ hvelocity_smooth hnavier_stokes b hb t ht x]
  rfl

end Review398
