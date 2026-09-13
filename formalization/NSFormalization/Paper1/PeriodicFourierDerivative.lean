import NSFormalization.Paper1.TorusCube

/-! The genuine coordinate derivative spectrum follows from the existing
periodic cube integration-by-parts theorem, with no assumed Fourier identity. -/
noncomputable section
namespace NSFormalization.Paper1
open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal BigOperators

/-- The angular-frequency linear phase on physical Euclidean space. -/
def periodicPhase (k : PeriodicFrequency) : Space →L[ℝ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ) • ∑ i : Fin 3,
    (k i : ℂ) • (Complex.ofRealCLM.comp (EuclideanSpace.proj i))

 theorem periodicPhase_apply (k : PeriodicFrequency) (x : Space) :
    periodicPhase k x = (2 * Real.pi * Complex.I : ℂ) * ∑ i : Fin 3, (k i : ℂ) * (x i : ℂ) := by
  simp [periodicPhase, smul_eq_mul]

 theorem periodicPhase_coordinate (k : PeriodicFrequency) (i : Fin 3) :
    periodicPhase k (coordinateVector i) = (2 * Real.pi * Complex.I : ℂ) * (k i : ℂ) := by
  rw [periodicPhase_apply]
  simp [coordinateVector, apply_ite]

def periodicCharacter (k : PeriodicFrequency) (x : Space) : ℂ := Complex.exp (periodicPhase k x)

 theorem periodicCharacter_eq_mFourier (k : PeriodicFrequency) (x : Space) :
    periodicCharacter k x = UnitAddTorus.mFourier k (fun i => (x i : AddCircle (1 : ℝ))) := by
  change Complex.exp (periodicPhase k x) = ∏ i : Fin 3, fourier (k i) (x i : AddCircle (1 : ℝ))
  rw [periodicPhase_apply, Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [fourier_coe_apply]
  congr 1
  simp only [Complex.ofReal_one, div_one]
  ring

 theorem periodicCharacter_smooth (k : PeriodicFrequency) : ContDiff ℝ ∞ (periodicCharacter k) :=
  (periodicPhase k).contDiff.cexp

 theorem periodicCharacter_periodic (k : PeriodicFrequency) : UnitPeriods (periodicCharacter k) := by
  intro x i
  simp only [periodicCharacter, map_add, Complex.exp_add, periodicPhase_coordinate]
  rw [mul_comm (2 * Real.pi * Complex.I : ℂ) (k i : ℂ),
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

 theorem spatialPartial_periodicCharacter (k : PeriodicFrequency) (i : Fin 3) (x : Space) :
    spatialPartial i (periodicCharacter k) x =
      ((2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)) * periodicCharacter k x := by
  unfold spatialPartial
  change (fderiv ℝ (fun y => Complex.exp (periodicPhase k y)) x) (coordinateVector i) = _
  rw [(periodicPhase k).hasFDerivAt.cexp.fderiv]
  simp only [smul_apply, smul_eq_mul, periodicPhase_coordinate,
    periodicCharacter, mul_comm]

 theorem periodicFourierCoeff_eq_cube (f : Space → ℂ) (k : PeriodicFrequency) :
    periodicFourierCoeff f k = cubeIntegral (fun x => periodicCharacter (-k) x * f x) := by
  rw [← integral_torusLift (fun x => periodicCharacter (-k) x * f x)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have hz := (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).symm_apply_apply z
  change (fun i => (((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val i) :
    AddCircle (1 : ℝ))) = z at hz
  simp only [torusLift, periodicCharacter_eq_mFourier, toSpace_apply, hz, smul_eq_mul]

 theorem spatialPartial_comp_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => L (f y)) x = L (spatialPartial i f x) := by
  unfold spatialPartial
  change (fderiv ℝ (L ∘ f) x) (coordinateVector i) = _
  rw [(L.hasFDerivAt.comp x ((hf.differentiable (by norm_num) x).hasFDerivAt)).fderiv]
  rfl

/-- The source real periodic integration theorem extended by the two coordinate
functionals of the complex plane. -/
theorem cubeIntegral_complex_partial_eq_zero {f : Space → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : UnitPeriods f) (i : Fin 3) : cubeIntegral (spatialPartial i f) = 0 := by
  apply Complex.ext
  · change (cubeIntegral (spatialPartial i f)).re = 0
    change Complex.reCLM (∫ y, spatialPartial i f (toSpace y) ∂cubeMeasure) = 0
    rw [← Complex.reCLM.integral_comp_comm (integrable_cube (continuous_partial hf i))]
    change cubeIntegral (fun x => (spatialPartial i f x).re) = 0
    have hpart : (fun x => (spatialPartial i f x).re) =
        spatialPartial i (fun x => (f x).re) :=
      funext (fun x => (spatialPartial_comp_clm Complex.reCLM hf i x).symm)
    rw [hpart]
    exact cubeIntegral_partial_eq_zero (Complex.reCLM.contDiff.comp hf)
      (fun x j => congrArg Complex.re (hp x j)) i
  · change (cubeIntegral (spatialPartial i f)).im = 0
    change Complex.imCLM (∫ y, spatialPartial i f (toSpace y) ∂cubeMeasure) = 0
    rw [← Complex.imCLM.integral_comp_comm (integrable_cube (continuous_partial hf i))]
    change cubeIntegral (fun x => (spatialPartial i f x).im) = 0
    have hpart : (fun x => (spatialPartial i f x).im) =
        spatialPartial i (fun x => (f x).im) :=
      funext (fun x => (spatialPartial_comp_clm Complex.imCLM hf i x).symm)
    rw [hpart]
    exact cubeIntegral_partial_eq_zero (Complex.imCLM.contDiff.comp hf)
      (fun x j => congrArg Complex.im (hp x j)) i

/-- Exact angular-frequency spectrum of an actual physical coordinate derivative. -/
theorem periodicFourierCoeff_spatialPartial {f : Space → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : UnitPeriods f) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (spatialPartial i f) k =
      ((2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)) * periodicFourierCoeff f k := by
  let χ := periodicCharacter (-k)
  have hχ : ContDiff ℝ 1 χ := (periodicCharacter_smooth (-k)).of_le (by norm_num)
  have hzero := cubeIntegral_complex_partial_eq_zero (hχ.mul hf)
    (fun x j => by
      change periodicCharacter (-k) (x + coordinateVector j) * f (x + coordinateVector j) = _
      rw [(periodicCharacter_periodic (-k)) x j, hp x j]) i
  have hd (x : Space) : spatialPartial i (fun y => χ y * f y) x =
      -((2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)) * (χ x * f x) +
      χ x * spatialPartial i f x := by
    unfold spatialPartial
    change (fderiv ℝ (χ * f) x) (coordinateVector i) = _
    rw [((hχ.differentiable (by norm_num) x).hasFDerivAt.mul
      (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    change χ x * spatialPartial i f x + f x * spatialPartial i χ x = _
    rw [spatialPartial_periodicCharacter]
    simp only [Pi.neg_apply, Int.cast_neg]
    dsimp [χ, spatialPartial]
    ring
  have hdFun : spatialPartial i (fun y => χ y * f y) = fun x =>
      -((2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)) * (χ x * f x) +
      χ x * spatialPartial i f x := funext hd
  rw [hdFun] at hzero
  unfold cubeIntegral at hzero
  dsimp only at hzero
  have hi1 : Integrable (fun y : Coords =>
      -((2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)) * (χ (toSpace y) * f (toSpace y))) cubeMeasure :=
    integrable_cube ((hχ.continuous.mul hf.continuous).const_mul _)
  have hi2 : Integrable (fun y : Coords => χ (toSpace y) * spatialPartial i f (toSpace y)) cubeMeasure :=
    integrable_cube (hχ.continuous.mul (continuous_partial hf i))
  rw [integral_add hi1 hi2, integral_const_mul] at hzero
  rw [periodicFourierCoeff_eq_cube, periodicFourierCoeff_eq_cube]
  change cubeIntegral (fun x => χ x * spatialPartial i f x) = _
  have heq := eq_neg_of_add_eq_zero_right hzero
  simpa only [cubeIntegral, neg_mul, neg_neg] using heq

end NSFormalization.Paper1
