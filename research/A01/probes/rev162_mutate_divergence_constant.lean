import NSFormalization.Section4.A01.ConstructorDivergence

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space spatialDivergence)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLpTranslation
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.A01
open scoped ContDiff

set_option autoImplicit false in
/-- Negative mutation: changing the required divergence constant from `0` to `1` must fail. -/
example {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (t : Icc (0 : ℝ) T) (θ : AddCircle (1 : ℝ)),
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (Z : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hZ : ∀ t, (Z t).field =ᵐ[volume] ⇑(U t))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T,
      (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hslice_contDiff : ∀ t ∈ Ico (0 : ℝ) T,
      ContDiff ℝ ∞ (fun x : Space => velocity (t, x))) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 1 := by
  exact divergence_of_cylinder_pointwise_of_contDiff
    u U hu hU hdiv Z hZ velocity hslice hslice_contDiff
