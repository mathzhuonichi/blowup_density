import NavierStokes.R3PressureFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Gaussian kernels for regularizing the whole-space pressure

The spatial second derivatives of a Gaussian are integrable. Their Fourier
transforms provide smooth approximations to the second-order Riesz symbol.
-/

noncomputable section
namespace NavierStokes.R3GaussianPressure

open Set Filter MeasureTheory ProblemStatement FourierTransform InnerProductSpace
open scoped Topology RealInnerProductSpace

def gaussianReal (a : ℝ) (x : Space) : ℝ := Real.exp (-a * ‖x‖ ^ 2)
def gaussian (a : ℝ) (x : Space) : ℂ := (gaussianReal a x : ℝ)
def firstGaussian (a : ℝ) (i : Fin 3) (x : Space) : ℂ :=
  ((-2 * a * x i * gaussianReal a x : ℝ) : ℂ)
def secondGaussian (a : ℝ) (i j : Fin 3) (x : Space) : ℂ :=
  (((4 * a ^ 2 * x i * x j - 2 * a * (if i = j then 1 else 0)) * gaussianReal a x : ℝ) : ℂ)

theorem gaussianReal_pos (a : ℝ) (x : Space) : 0 < gaussianReal a x := Real.exp_pos _

theorem gaussianReal_contDiff (a : ℝ) : ContDiff ℝ ⊤ (gaussianReal a) := by
  exact (contDiff_const.mul (contDiff_norm_sq ℝ)).exp

theorem gaussian_contDiff (a : ℝ) : ContDiff ℝ ⊤ (gaussian a) :=
  Complex.ofRealCLM.contDiff.comp (gaussianReal_contDiff a)

theorem firstGaussian_contDiff (a : ℝ) (i : Fin 3) : ContDiff ℝ ⊤ (firstGaussian a i) := by
  have h := gaussianReal_contDiff a
  change ContDiff ℝ ⊤ (Complex.ofRealCLM ∘ (fun x : Space => -2 * a * x i * gaussianReal a x))
  apply Complex.ofRealCLM.contDiff.comp
  fun_prop

theorem gaussian_moment_integrable {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun x : Space => ‖x‖ ^ k * gaussianReal a x) := by
  apply (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r => r ^ k * Real.exp (-a * r ^ 2))).mpr
  have hi := integrableOn_rpow_mul_exp_neg_mul_sq ha
    (s := 2 + (k : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) k] : (-1 : ℝ) < 2 + (k : ℝ))
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  rw [Real.rpow_add hr, Real.rpow_two, Real.rpow_natCast]
  ring

theorem gaussianReal_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussianReal a) := by
  simpa using gaussian_moment_integrable ha 0

theorem gaussian_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussian a) :=
  Complex.ofRealCLM.integrable_comp (gaussianReal_integrable ha)

theorem firstGaussian_integrable {a : ℝ} (ha : 0 < a) (i : Fin 3) :
    Integrable (firstGaussian a i) := by
  apply ((gaussian_moment_integrable ha 1).const_mul (2 * a)).mono'
    (firstGaussian_contDiff a i).continuous.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  simp only [firstGaussian, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_pos ha, abs_of_pos (gaussianReal_pos a x), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), pow_one]
  have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * a)) (gaussianReal_pos a x).le
  nlinarith

theorem secondGaussian_contDiff (a : ℝ) (i j : Fin 3) : ContDiff ℝ ⊤ (secondGaussian a i j) := by
  have h := gaussianReal_contDiff a
  change ContDiff ℝ ⊤ (Complex.ofRealCLM ∘ (fun x : Space =>
    (4 * a ^ 2 * x i * x j - 2 * a * (if i = j then 1 else 0)) * gaussianReal a x))
  apply Complex.ofRealCLM.contDiff.comp
  fun_prop

theorem secondGaussian_integrable {a : ℝ} (ha : 0 < a) (i j : Fin 3) :
    Integrable (secondGaussian a i j) := by
  apply (((gaussian_moment_integrable ha 2).const_mul (4 * a ^ 2)).add
    ((gaussianReal_integrable ha).const_mul (2 * a))).mono'
    (secondGaussian_contDiff a i j).continuous.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  simp only [secondGaussian, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (gaussianReal_pos a x)]
  have hij : |(if i = j then 1 else 0 : ℝ)| ≤ 1 := by split <;> norm_num
  have hprod : |x i| * |x j| ≤ ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, pow_two] using
      mul_le_mul (PiLp.norm_apply_le x i) (PiLp.norm_apply_le x j)
        (norm_nonneg (x j)) (norm_nonneg x)
  have hb : |4 * a ^ 2 * x i * x j - 2 * a * (if i = j then 1 else 0 : ℝ)| ≤
      4 * a ^ 2 * ‖x‖ ^ 2 + 2 * a := by
    calc
      _ ≤ |4 * a ^ 2 * x i * x j| + |2 * a * (if i = j then 1 else 0 : ℝ)| := abs_sub _ _
      _ = 4 * a ^ 2 * (|x i| * |x j|) + 2 * a * |(if i = j then 1 else 0 : ℝ)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos ha, abs_pow]
        norm_num
        ring
      _ ≤ _ := by nlinarith
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right hb (gaussianReal_pos a x).le]

theorem hasFDerivAt_gaussianReal (a : ℝ) (x : Space) :
    HasFDerivAt (gaussianReal a) ((-2 * a * gaussianReal a x) • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-a)).exp
  convert! h using 1
  ext y
  simp only [smul_apply, smul_eq_mul, gaussianReal]
  ring

theorem gaussian_partial (a : ℝ) (i : Fin 3) (x : Space) :
    fderiv ℝ (gaussian a) x (coordinateVector i) = firstGaussian a i x := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_gaussianReal a x)
  rw [show gaussian a = Complex.ofRealCLM ∘ gaussianReal a from rfl, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply, Complex.ofRealCLM_apply]
  have hi : ⟪x, coordinateVector i⟫_ℝ = x i := by
    simp [coordinateVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [hi]
  unfold firstGaussian
  push_cast
  ring

theorem firstGaussian_partial (a : ℝ) (i j : Fin 3) (x : Space) :
    fderiv ℝ (firstGaussian a i) x (coordinateVector j) = secondGaussian a i j x := by
  have hp := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h := ((hp.const_mul (-2 * a)).mul (hasFDerivAt_gaussianReal a x))
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x h
  change (fderiv ℝ (Complex.ofRealCLM ∘
    ((fun y : Space => (-2 * a) * (EuclideanSpace.proj i) y) * gaussianReal a)) x)
      (coordinateVector j) = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply]
  have hi : ⟪x, coordinateVector j⟫_ℝ = x j := by
    simp [coordinateVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simp only [hi]
  change Complex.ofReal ((-2 * a * x i) * ((-2 * a * gaussianReal a x) * x j) +
    gaussianReal a x * ((-2 * a) * (coordinateVector j) i)) = _
  have hij : (coordinateVector j) i = if i = j then 1 else 0 := by
    simp [coordinateVector]
  rw [hij]
  unfold secondGaussian
  congr 1
  ring


/-- Fourier differentiation in one direction only needs integrability of
that directional derivative. -/
theorem fourier_directional_derivative {f : Space → ℂ} (v ξ : Space)
    (hf : Integrable f) (hfd : Differentiable ℝ f)
    (hfi : Integrable (fun x => fderiv ℝ f x v)) :
    𝓕 (fun x => fderiv ℝ f x v) ξ =
      (2 * (Real.pi : ℂ) * Complex.I * (⟪v, ξ⟫_ℝ : ℂ)) * 𝓕 f ξ := by
  let c (x : Space) : ℂ := Real.fourierChar (-⟪x, ξ⟫_ℝ)
  have hc : Integrable (fun x => c x * f x) := by
    simpa only [c, Circle.smul_def, smul_eq_mul] using (Real.fourierIntegral_convergent_iff ξ).2 hf
  have hcp : Integrable (fun x => c x * fderiv ℝ f x v) := by
    simpa only [c, Circle.smul_def, smul_eq_mul] using (Real.fourierIntegral_convergent_iff ξ).2 hfi
  have hd (x : Space) : fderiv ℝ c x v =
      -(2 * (Real.pi : ℂ) * Complex.I * (⟪v, ξ⟫_ℝ : ℂ)) * c x := by
    simpa only [c, innerSL_apply_apply ℝ, neg_mul] using
      Real.fderiv_fourierChar_neg_bilinear_left_apply (innerSL ℝ) x v ξ
  have hdint : Integrable (fun x => fderiv ℝ c x v * f x) := by
    simp only [hd, mul_assoc]
    exact hc.const_mul _
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdint hcp hc
    (fun _ _ => (Real.differentiable_fourierChar_neg_bilinear_left (innerSL ℝ) ξ).differentiableAt)
    (fun _ _ => hfd.differentiableAt)
  simp only [hd, mul_assoc, integral_const_mul, neg_mul, integral_neg, neg_neg] at hi
  simpa only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, c, mul_assoc] using hi

theorem fourier_firstGaussian {a : ℝ} (ha : 0 < a) (i : Fin 3) (ξ : Space) :
    𝓕 (firstGaussian a i) ξ = (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ)) * 𝓕 (gaussian a) ξ := by
  have hi : ⟪coordinateVector i, ξ⟫_ℝ = ξ i := by
    rw [real_inner_comm]
    simp [coordinateVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  simpa only [gaussian_partial, hi] using
    fourier_directional_derivative (coordinateVector i) ξ (gaussian_integrable ha)
      ((gaussian_contDiff a).differentiable (by simp))
      (by simpa only [gaussian_partial] using firstGaussian_integrable ha i)

theorem fourier_secondGaussian {a : ℝ} (ha : 0 < a) (i j : Fin 3) (ξ : Space) :
    𝓕 (secondGaussian a i j) ξ =
      (-4 * (Real.pi : ℂ) ^ 2 * (ξ i : ℂ) * (ξ j : ℂ)) * 𝓕 (gaussian a) ξ := by
  have hj : ⟪coordinateVector j, ξ⟫_ℝ = ξ j := by
    rw [real_inner_comm]
    simp [coordinateVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  have hh := fourier_directional_derivative (coordinateVector j) ξ (firstGaussian_integrable ha i)
    ((firstGaussian_contDiff a i).differentiable (by simp))
    (by simpa only [firstGaussian_partial] using secondGaussian_integrable ha i j)
  simp only [firstGaussian_partial, hj, fourier_firstGaussian ha] at hh
  rw [hh]
  calc
    _ = (4 * (Real.pi : ℂ) ^ 2 * (ξ i : ℂ) * (ξ j : ℂ) * Complex.I ^ 2) *
        𝓕 (gaussian a) ξ := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The classical Gaussian Fourier formula with real parameters. -/
theorem fourier_gaussian {a : ℝ} (ha : 0 < a) (ξ : Space) :
    𝓕 (gaussian a) ξ =
      (((Real.pi / a) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi ^ 2) * ‖ξ‖ ^ 2 / a) : ℝ) : ℂ) := by
  have hh := fourier_gaussian_innerProductSpace (V := Space)
    (b := (a : ℂ)) (by simpa using ha) ξ
  have he : (fun x : Space => Complex.exp (-(a : ℂ) * ‖x‖ ^ 2)) = gaussian a := by
    funext x
    simp [gaussian, gaussianReal, Complex.ofReal_exp]
  rw [he] at hh
  rw [hh]
  norm_num only [finrank_euclideanSpace, Fintype.card_fin]
  have hp : ((Real.pi / a : ℝ) : ℂ) ^ (3 / 2 : ℂ) =
      (((Real.pi / a) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (y := (3 / 2 : ℝ)) (by positivity : 0 ≤ Real.pi / a)).symm
  rw [← Complex.ofReal_div, hp]
  push_cast
  rfl

end NavierStokes.R3GaussianPressure
