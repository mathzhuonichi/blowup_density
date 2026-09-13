import NSFormalization.Paper1.PeriodicExplicitShearCertificate
import NSFormalization.Paper1.PeriodicShearLocal

noncomputable section
namespace NSFormalization.Paper1.PeriodicSingleModeLocal
open Set
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicShearLocal
open NSFormalization.Paper1.PeriodicExplicitShearCertificate
open scoped ContDiff ENNReal

private def heatFactor (ν b t : ℝ) : ℝ := Real.exp (-(ν * b ^ 2) * t)
private def mode (A ν b : ℝ) : VelocityField := fun z =>
  (A * heatFactor ν b z.1 * Real.sin (b * z.2 1)) • coordinateVector 0

private lemma smooth_coordinate (s : Set SpaceTime) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime => z.2 1) s := by
  let P : Space →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 3)
  have hp : ContDiffOn ℝ ∞ (fun _ : SpaceTime => P) s := contDiffOn_const
  have hs : ContDiffOn ℝ ∞ (fun z : SpaceTime => z.2) s := contDiffOn_snd
  simpa [P] using hp.clm_apply hs

private lemma smooth_mode (A ν b : ℝ) :
    ContDiffOn ℝ ∞ (mode A ν b) (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  let s : Set SpaceTime := Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)
  have ht : ContDiffOn ℝ ∞ (fun z : SpaceTime => z.1) s := contDiffOn_fst
  have hx : ContDiffOn ℝ ∞ (fun z : SpaceTime => z.2 1) s := smooth_coordinate s
  have he : ContDiffOn ℝ ∞ (fun z : SpaceTime => heatFactor ν b z.1) s := by
    apply ContDiffOn.exp
    have hlin := (contDiffOn_const (c := -(ν * b ^ 2))).mul ht
    simpa [heatFactor, mul_assoc] using hlin
  have hs : ContDiffOn ℝ ∞ (fun z : SpaceTime => Real.sin (b * z.2 1)) s := by
    apply ContDiffOn.sin
    exact (contDiffOn_const.mul hx)
  have ham : ContDiffOn ℝ ∞ (fun z : SpaceTime => A * heatFactor ν b z.1 * Real.sin (b * z.2 1)) s :=
    (contDiffOn_const.mul he).mul hs
  have hv := ham.smul_const (coordinateVector 0)
  change ContDiffOn ℝ ∞ (fun z : SpaceTime =>
    (A * heatFactor ν b z.1 * Real.sin (b * z.2 1)) • coordinateVector 0) s
  simpa [heatFactor] using hv

private lemma temporal_mode (A ν b t : ℝ) (x : Space) :
    temporalDerivative (mode A ν b) t x =
      (-(ν * b ^ 2)) • mode A ν b (t, x) := by
  unfold temporalDerivative mode heatFactor
  have hlin : HasDerivAt (fun s : ℝ => -(ν * b ^ 2) * s)
      (-(ν * b ^ 2)) t := by
    simpa using (hasDerivAt_id t).const_mul (-(ν * b ^ 2))
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(ν * b ^ 2) * s))
      (Real.exp (-(ν * b ^ 2) * t) * (-(ν * b ^ 2))) t := hlin.exp
  have ham := (hexp.const_mul A).mul_const (Real.sin (b * x 1))
  have hv := ham.smul_const (coordinateVector 0)
  have hf := hv.hasFDerivAt
  have hfd := hf.fderiv
  change (fderiv ℝ (fun s : ℝ =>
      (A * Real.exp (-(ν * b ^ 2) * s) * Real.sin (b * x 1)) • coordinateVector 0) t) 1 = _
  rw [hfd]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  ext j
  fin_cases j <;> simp [coordinateVector, smul_eq_mul] <;> ring

private lemma spatial_mode (A ν b t : ℝ) (x : Space) :
    spatialLaplacian (mode A ν b) t x =
      -(b ^ 2) • mode A ν b (t, x) := by
  change spatialLaplacian (fun z =>
    ((A * heatFactor ν b t) * Real.sin (b * z.2 1)) • coordinateVector 0) t x =
      -(b ^ 2) • (((A * heatFactor ν b t) * Real.sin (b * x 1)) • coordinateVector 0)
  convert shear_laplacian_eigen (A * heatFactor ν b t) b t x using 1 <;> rfl


private theorem heat_balance_mode (A ν b t : ℝ) (x : Space) :
    temporalDerivative (mode A ν b) t x =
      ν • spatialLaplacian (mode A ν b) t x := by
  rw [temporal_mode, spatial_mode]
  simp only [smul_smul]
  congr 1
  ring

/-- A fully explicit nonconstant local flow certificate for one transverse
Fourier mode.  The exponential factor is the exact heat evolution, so the
nonlinear transport remains zero and the displayed profile solves the
unforced equation on `(0,1)`. -/
def singleModeHeatProfile (ν A : ℝ) : ShearHeatProfile ν 1 where
  velocity := mode A ν (2 * Real.pi)
  pressure := fun _ => 0
  horizon_pos := by norm_num
  velocity_smooth := by
    simpa only [show (1 : ℝ) = 1 from rfl] using smooth_mode A ν (2 * Real.pi)
  pressure_smooth := contDiffOn_const
  velocity_periodic := by
    intro t ht x i
    fin_cases i
    · simp [mode, heatFactor, coordinateVector]
    · have h := shear_periodic_two_pi (A * heatFactor ν (2 * Real.pi) t)
        (S := 1) t ht x
      have h1 := h 1
      change ((A * heatFactor ν (2 * Real.pi) t) * Real.sin (2 * Real.pi * ((x + coordinateVector 1) 1))) • coordinateVector 0 =
        ((A * heatFactor ν (2 * Real.pi) t) * Real.sin (2 * Real.pi * (x 1))) • coordinateVector 0
      convert h1 using 1 <;> rfl
    · simp [mode, heatFactor, coordinateVector]
  pressure_periodic := by intro t ht x i; rfl
  initial_data := fun x =>
    (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0
  initial := by
    intro x
    simp [mode, heatFactor]
  divergence_free := by
    intro t ht x
    change spatialDivergence (fun z =>
      ((A * heatFactor ν (2 * Real.pi) t) * Real.sin (2 * Real.pi * z.2 1)) • coordinateVector 0) t x = 0
    convert shear_divergence_zero (A * heatFactor ν (2 * Real.pi) t) (2 * Real.pi) t x using 1 <;> rfl
  transport_free := by
    intro t ht x
    change advection (fun z =>
      ((A * heatFactor ν (2 * Real.pi) t) * Real.sin (2 * Real.pi * z.2 1)) • coordinateVector 0) t x = 0
    convert shear_advection_zero (A * heatFactor ν (2 * Real.pi) t) (2 * Real.pi) t x using 1 <;> rfl
  heat_balance := by
    intro t ht x
    exact heat_balance_mode A ν (2 * Real.pi) t x
  pressure_flat := by
    intro t ht x
    simp [pressureGradient]

/-- The explicit single transverse mode produces a genuine unforced periodic
flow for every viscosity and amplitude, on the unit time interval. -/
theorem singleModeHeatFlow (ν A : ℝ) :
    Nonempty (NSFormalization.Paper1.PeriodicLifespan.Flow ν
      (fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0)
      (0 : VelocityField) 1) := by
  exact shearHeatProfile_nonempty (singleModeHeatProfile ν A)


end NSFormalization.Paper1.PeriodicSingleModeLocal
