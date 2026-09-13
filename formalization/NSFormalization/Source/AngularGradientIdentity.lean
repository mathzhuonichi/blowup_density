import NSFormalization.Source.AngularForceNorms
import NSFormalization.Paper3.PositiveFourierTime

/-! Exact inhomogeneous Sobolev/gradient identity in the unitary angular
Fourier convention. The derivatives are the actual spatial Frechet derivatives. -/
noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory
open NavierStokesR3.HarmonicTestFunctionals
open scoped ContDiff FourierTransform

def angularFrequencyEquiv : Space ≃L[ℝ] Space where
  toFun x := frequencyUnit⁻¹ • x
  invFun x := frequencyUnit • x
  left_inv x := by simp [smul_smul, frequencyUnit_pos.ne']
  right_inv x := by simp [smul_smul, frequencyUnit_pos.ne']
  map_add' x y := smul_add _ x y
  map_smul' a x := by simp [smul_smul, mul_comm]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def angularSchwartz (φ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  frequencyUnit ^ (-3 / 2 : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ angularFrequencyEquiv (𝓕 φ)

theorem angularSchwartz_coe (φ : SchwartzMap Space ℂ) :
    (angularSchwartz φ : Space → ℂ) = angularFourier (φ : Space → ℂ) := rfl

theorem angular_bessel_integrable (s : ℝ) (φ : SchwartzMap Space ℂ) :
    Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s *
      ‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2) :=
  Paper3.schwartz_bessel_integrable s (angularSchwartz φ)

theorem fourier_partial_norm_sq (φ : SchwartzMap Space ℂ) (ξ : Space) (i : Fin 3) :
    ‖𝓕 (partialCLM i φ) ξ‖ ^ 2 = frequencyUnit ^ 2 * (ξ i) ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
  have hn := congrArg norm (fourier_partialCLM_apply i φ ξ)
  change ‖𝓕 (partialCLM i φ) ξ‖ =
    ‖(2 : ℂ) * ↑Real.pi * Complex.I * ↑(ξ i) * 𝓕 φ ξ‖ at hn
  rw [hn]
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num [frequencyUnit, mul_pow, sq_abs]

/-- The normalization cancels the factor 2*pi from Mathlib's derivative rule. -/
theorem angular_partial_norm_sq (φ : SchwartzMap Space ℂ) (ξ : Space) (i : Fin 3) :
    ‖angularFourier (partialCLM i φ : Space → ℂ) ξ‖ ^ 2 =
      (ξ i) ^ 2 * ‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2 := by
  unfold angularFourier
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [show ‖𝓕 (partialCLM i φ : Space → ℂ) (frequencyUnit⁻¹ • ξ)‖ ^ 2 =
    frequencyUnit ^ 2 * ((frequencyUnit⁻¹ • ξ) i) ^ 2 * ‖𝓕 φ (frequencyUnit⁻¹ • ξ)‖ ^ 2
      from fourier_partial_norm_sq φ (frequencyUnit⁻¹ • ξ) i]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, inv_pow]
  simp only [SchwartzMap.fourier_coe]
  field_simp [frequencyUnit_pos.ne']

theorem angularSobolevSq_nonneg (s : ℝ) (f : Space → ℂ) : 0 ≤ angularSobolevSq s f :=
  integral_nonneg (fun _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))

/-- Exact identity H^(s+1)^2 = H^s^2 + sum_i H^s(partial_i)^2. -/
theorem angular_succ_energy (s : ℝ) (φ : SchwartzMap Space ℂ) :
    angularSobolevSq (s + 1) (φ : Space → ℂ) =
      angularSobolevSq s (φ : Space → ℂ) +
        ∑ i : Fin 3, angularSobolevSq s (partialCLM i φ : Space → ℂ) := by
  have hp (ξ : Space) : (1 + ‖ξ‖ ^ 2) ^ (s + 1) * ‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2 =
      (1 + ‖ξ‖ ^ 2) ^ s * ‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2 +
        ∑ i : Fin 3, (1 + ‖ξ‖ ^ 2) ^ s * ‖angularFourier (partialCLM i φ : Space → ℂ) ξ‖ ^ 2 := by
    rw [Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖ ^ 2), Real.rpow_one]
    simp_rw [angular_partial_norm_sq]
    have hn : ‖ξ‖ ^ 2 = ∑ i : Fin 3, (ξ i) ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    rw [hn]
    simp only [Fin.sum_univ_succ]
    ring
  unfold angularSobolevSq
  simp_rw [hp]
  rw [integral_add (angular_bessel_integrable s φ)
    (integrable_finsetSum _ (fun i _ => angular_bessel_integrable s (partialCLM i φ))),
    integral_finsetSum _ (fun i _ => angular_bessel_integrable s (partialCLM i φ))]

theorem angularSobolevSq_succ (s : ℝ) {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    angularSobolevSq (s + 1) f = angularSobolevSq s f +
      ∑ i : Fin 3, angularSobolevSq s (NavierStokes.PeriodicIntegration.spatialPartial i f) :=
  angular_succ_energy s (NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc)

/-- This is the squared norm of the actual componentwise physical gradient. -/
def vectorAngularGradientSq (s : ℝ) (F : VelocityField) (t : ℝ) : ℝ :=
  ∑ j : Fin 3, ∑ i : Fin 3, angularSobolevSq s
    (NavierStokes.PeriodicIntegration.spatialPartial i (fun x => coordinateForce F j (t, x)))

theorem vectorAngularSobolev_succ (s : ℝ) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    (vectorAngularSobolevNorm (s + 1) F t) ^ 2 =
      (vectorAngularSobolevNorm s F t) ^ 2 + vectorAngularGradientSq s F t := by
  unfold vectorAngularSobolevNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => angularSobolevSq_nonneg _ _)),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => angularSobolevSq_nonneg _ _))]
  have he (j : Fin 3) := angularSobolevSq_succ s (f := fun x => coordinateForce F j (t, x))
    ((coordinateForce_smooth hF j).comp (contDiff_const.prodMk contDiff_id))
    (Paper3.compact_spatial_slice (coordinateForce_compact hc j) t)
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  rfl

/-- The exact Y²+Z² identity used by the finite-horizon critical argument. -/
theorem critical_inhomogeneous_identity {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    (vectorAngularSobolevNorm (3 / 2) F t) ^ 2 =
      (vectorAngularSobolevNorm (1 / 2) F t) ^ 2 + vectorAngularGradientSq (1 / 2) F t := by
  convert vectorAngularSobolev_succ (1 / 2) hF hc t using 1
  norm_num

end NSFormalization.Source
