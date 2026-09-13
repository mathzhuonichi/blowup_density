import NSFormalization.Paper3.AllOrderFourierTime

/-!
# Actual Sobolev vectors represented in weighted Fourier L²

The map below sends the original compact smooth function to an actual element
of the Hilbert space `Lp ℂ 2 volume`. Its representative is the Bessel weight
times the actual Fourier transform, and its norm is exactly the previously used
scalar Fourier Sobolev norm. All differentiability below is over the reals.
-/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-- The weighted Fourier transform, followed by the genuine L² quotient map. -/
def weightedFourierLp (s : ℝ) : SchwartzMap Space ℂ →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  (SchwartzMap.toLpCLM ℝ ℂ 2 volume).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2))).comp
      ((fourierCLE ℂ (SchwartzMap Space ℂ)).toContinuousLinearMap.restrictScalars ℝ))

/-- Its actual a.e. representative is the weighted Fourier transform. -/
theorem weightedFourierLp_ae (s : ℝ) (φ : SchwartzMap Space ℂ) :
    (weightedFourierLp s φ : Space → ℂ) =ᵐ[volume]
      (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2) • 𝓕 (φ : Space → ℂ) ξ) := by
  change (((SchwartzMap.smulLeftCLM ℂ (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2))
    (𝓕 φ)).toLp 2 volume) : Space → ℂ) =ᵐ[volume] _
  have h := SchwartzMap.coeFn_toLp
    (SchwartzMap.smulLeftCLM ℂ (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) (𝓕 φ)) 2 volume
  simpa only [weightedFourierLp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars, ContinuousLinearEquiv.coe_coe,
    SchwartzMap.toLpCLM_apply, SchwartzMap.smulLeftCLM_apply
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow Space (s / 2)),
    SchwartzMap.fourier_coe] using h

/-- The Hilbert-space norm is exactly the square root of the weighted Fourier
energy, with no assumption equating an abstract norm to the manuscript quantity. -/
theorem norm_weightedFourierLp (s : ℝ) (φ : SchwartzMap Space ℂ) :
    ‖weightedFourierLp s φ‖ = NSFormalization.Source.fourierSobolevNorm s (φ : Space → ℂ) := by
  let ψ : SchwartzMap Space ℂ := SchwartzMap.smulLeftCLM ℂ
    (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) (𝓕 φ)
  have heq (ξ : Space) : ‖ψ ξ‖ ^ 2 = besselIntegrand s (𝓕 (φ : Space → ℂ)) ξ := by
    rw [show ψ ξ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) • 𝓕 (φ : Space → ℂ) ξ from
      SchwartzMap.smulLeftCLM_apply_apply
        (Function.hasTemperateGrowth_one_add_norm_sq_rpow Space (s / 2)) (𝓕 φ) ξ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2)]
    simp only [Nat.cast_ofNat, div_mul_cancel₀ s (by norm_num : (2 : ℝ) ≠ 0)]
    rfl
  change ‖ψ.toLp 2 volume‖ = _
  rw [SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  try norm_num only [ENNReal.toReal_ofNat, Real.rpow_natCast]
  rw [← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, heq]
  rfl

/-- Original compact smooth inputs are mapped explicitly to the weighted L²
Sobolev representation. The hypotheses only certify the original function. -/
def compactFourierLp (s : ℝ) (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Lp ℂ 2 (volume : Measure Space) :=
  weightedFourierLp s (NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc)

 theorem norm_compactFourierLp (s : ℝ) (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ‖compactFourierLp s f hf hc‖ = NSFormalization.Source.fourierSobolevNorm s f :=
  norm_weightedFourierLp s _

end NSFormalization.Paper3
