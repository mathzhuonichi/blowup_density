import NSFormalization.Paper1.PeriodicShearLocal

/-!
# Explicit nonconstant periodic shear certificate

This file records the fully checked spatial part of a single transverse
Fourier mode.  The profile is nonconstant and periodic, has zero divergence
and zero transport, and its Laplacian is exactly the expected eigenvalue.
The remaining heat-time factor is intentionally left at the
`ShearHeatProfile` certificate boundary: it requires a separate endpoint
calculus lemma for the one-sided time derivative.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicExplicitShearCertificate

open Set
open NavierStokes NavierStokes.ProblemStatement
open scoped ContDiff

private def shear (A b : ℝ) : Space → Space := fun x =>
  (A * Real.sin (b * x 1)) • coordinateVector 0

private lemma hasFDeriv_sin_coord (b : ℝ) (x : Space) :
    HasFDerivAt (fun y : Space => Real.sin (b * y 1))
      ((b * Real.cos (b * x 1)) •
        (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)) x := by
  have hcoord : HasFDerivAt (fun y : Space => y 1)
      (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hlin := hcoord.const_mul b
  have hsin := hlin.sin
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hsin

private lemma hasFDeriv_cos_coord (b : ℝ) (x : Space) :
    HasFDerivAt (fun y : Space => Real.cos (b * y 1))
      ((-(Real.sin (b * x 1))) • b •
        (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)) x := by
  have hcoord : HasFDerivAt (fun y : Space => y 1)
      (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hlin := hcoord.const_mul b
  exact hlin.cos

private lemma shear_fderiv (A b : ℝ) (x v : Space) :
    fderiv ℝ (shear A b) x v =
      (A * b * Real.cos (b * x 1) * v 1) • coordinateVector 0 := by
  rw [show shear A b = (fun y : Space =>
      (A * Real.sin (b * y 1)) • coordinateVector 0) from rfl]
  rw [(((hasFDeriv_sin_coord b x).const_mul A).smul_const
    (coordinateVector 0)).fderiv]
  simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- The transverse Fourier shear has no nonlinear self-transport. -/
theorem shear_advection_zero (A b : ℝ) (t : ℝ) (x : Space) :
    advection (fun z => shear A b z.2) t x = 0 := by
  unfold advection spatialDerivative
  rw [shear_fderiv]
  simp [shear, coordinateVector]

/-- The transverse Fourier shear is divergence-free. -/
theorem shear_divergence_zero (A b : ℝ) (t : ℝ) (x : Space) :
    spatialDivergence (fun z => shear A b z.2) t x = 0 := by
  unfold spatialDivergence spatialDerivative
  simp_rw [shear_fderiv]
  simp [Fin.sum_univ_three, coordinateVector]

/-- The mode is an eigenfunction of the spatial Laplacian. -/
theorem shear_laplacian_eigen (A b : ℝ) (t : ℝ) (x : Space) :
    spatialLaplacian (fun z => shear A b z.2) t x =
      -(b ^ 2) • shear A b x := by
  unfold spatialLaplacian spatialDerivative
  simp_rw [shear_fderiv]
  have hd (i : Fin 3) :
      fderiv ℝ (fun y : Space =>
        (A * b * Real.cos (b * y 1) * (coordinateVector i) 1) • coordinateVector 0)
        x (coordinateVector i) =
        (- (A * b ^ 2 * Real.sin (b * x 1)) * ((coordinateVector i) 1) ^ 2) •
          coordinateVector 0 := by
    have hder := ((((hasFDeriv_cos_coord b x).const_smul (A * b)).mul_const
      ((coordinateVector i) 1)).smul_const (coordinateVector 0)).fderiv
    change (fderiv ℝ (fun y : Space =>
      ((A * b * Real.cos (b * y 1)) * (coordinateVector i) 1) • coordinateVector 0) x)
      (coordinateVector i) = _
    have hf : (fun y : Space =>
        (A * b * Real.cos (b * y 1) * (coordinateVector i) 1) • coordinateVector 0) =
      (fun y : Space =>
        (((A * b) • (fun y : Space => Real.cos (b * y 1))) y *
          (coordinateVector i) 1) • coordinateVector 0) := by
      funext y
      simp [smul_eq_mul]
    rw [hf, hder]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]
    fin_cases i <;> simp [coordinateVector] <;> ring
  simp_rw [hd]
  rw [Fin.sum_univ_three]
  ext j
  fin_cases j <;> simp [coordinateVector, shear, smul_smul] <;> ring

/-- A fixed unit period in the active coordinate when `b = 2π`. -/
theorem shear_periodic_two_pi (A : ℝ) {S : ℝ} :
    UnitSpatialPeriodsOn (Ico (0 : ℝ) S)
      (fun z => shear A (2 * Real.pi) z.2) := by
  intro t ht x i
  fin_cases i
  · simp [shear, coordinateVector]
  · change (A * Real.sin (2 * Real.pi * ((x + coordinateVector 1) 1))) • coordinateVector 0 =
      (A * Real.sin (2 * Real.pi * (x 1))) • coordinateVector 0
    congr 2
    have harg : 2 * Real.pi * ((x + coordinateVector 1) 1) =
        2 * Real.pi * (x 1) + 2 * Real.pi := by
      simp [coordinateVector]
      ring
    rw [harg, Real.sin_add_two_pi]
  · simp [shear, coordinateVector]

/-- Nonzero amplitude yields a nonzero value at a concrete point. -/
theorem shear_nonzero_at (A : ℝ) (hA : A ≠ 0) :
    shear A (2 * Real.pi) ((1 / 4 : ℝ) • coordinateVector 1) ≠ 0 := by
  intro h
  have hcoord := congrArg (fun y : Space => y 0) h
  simp [shear, coordinateVector] at hcoord
  have hs : Real.sin (2 * Real.pi * (4 : ℝ)⁻¹) = 1 := by
    rw [show 2 * Real.pi * (4 : ℝ)⁻¹ = Real.pi / 2 by ring, Real.sin_pi_div_two]
  simp [hs] at hcoord
  exact hA hcoord

end NSFormalization.Paper1.PeriodicExplicitShearCertificate
