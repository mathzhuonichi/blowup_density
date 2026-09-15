import NSFormalization.Section4.A01.ConstructorPressure

noncomputable section

namespace Rev168

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open scoped ContDiff

/-- Reviewer check: the hypothesis called `hprojected` by
`momentum_of_projected` is an algebraic consequence of the definition of `G`
and incompressibility; it is not the Leray/Duhamel equation `∂ₜu = P R`. -/
theorem pointwise_hprojected_is_redundant {T : ℝ} (ν : ℝ)
    (f velocity : VelocityField)
    (hvelocity : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence velocity t x = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative velocity t x - ν • spatialLaplacian velocity t x =
        (f (t, x) - convectionDivergence velocity t x) -
          pressureGradientOfVelocity ν f velocity (t, x) := by
  intro t ht x
  have htIco : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hu : DifferentiableAt ℝ (fun y : Space => velocity (t, y)) x :=
    ((NSFormalization.Section4.D01.contDiff_slice hvelocity htIco).differentiable
      (by simp)) x
  rw [convectionDivergence_eq_advection velocity t x hu (hdiv t htIco x)]
  simp only [pressureGradientOfVelocity, momentumResidualOfVelocity]
  abel

/-- Consequently the momentum conclusion needs curl-freeness of `G`, but not
the separately stated pointwise `hprojected` binder. -/
theorem momentum_without_pointwise_hprojected {T : ℝ} (ν : ℝ)
    (f velocity : VelocityField)
    (hvelocity : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence velocity t x = 0)
    (hgradient_smooth : ∀ t ∈ Ioo (0 : ℝ) T,
      ContDiff ℝ ∞ (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hgradient_symm : ∀ t ∈ Ioo (0 : ℝ) T,
      RadialPotential.HasSymmetricJacobian
        (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual
        ν velocity (pressureOfVelocity ν f velocity) t x = f (t, x) :=
  momentum_of_projected ν f velocity hvelocity hdiv hgradient_smooth hgradient_symm
    (pointwise_hprojected_is_redundant ν f velocity hvelocity hdiv)

/-- Positive-horizon non-vacuity: on the nonempty interval `(0,1)`, the
constructed zero pressure and zero velocity satisfy momentum with zero force. -/
example : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual
      1 (0 : VelocityField) (pressureOfVelocity 1 0 0) t x = 0 := by
  intro t _ht x
  rw [pressureOfVelocity_zero]
  simp [NavierStokesR3.ProblemStatement.navierStokesResidual,
    temporalDerivative, advection, spatialLaplacian, spatialDerivative,
    pressureGradient]

end Rev168
