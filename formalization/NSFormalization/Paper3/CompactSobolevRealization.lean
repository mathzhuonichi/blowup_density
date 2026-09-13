import NSFormalization.Paper3.SobolevHilbertModel

/-! The full distributional Sobolev Hilbert model agrees exactly with the
original compact smooth physical functions used in the insertion construction. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff ENNReal SchwartzMap

/-- Distributional Bessel multiplication agrees with actual pointwise
multiplication on Schwartz inputs. -/
theorem sobolevWeightMultiplier_schwartz (s : ℝ) (φ : SchwartzMap Space ℂ) :
    sobolevWeightMultiplier s (φ : 𝓢'(Space, ℂ)) =
      ((SchwartzMap.smulLeftCLM ℂ (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) φ) : 𝓢'(Space, ℂ)) := by
  ext ψ
  change (φ : 𝓢'(Space, ℂ)) (SchwartzMap.smulLeftCLM ℂ (sobolevBesselWeight s) ψ) = _
  simp only [SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply (sobolevBesselWeight_temperate s),
    SchwartzMap.smulLeftCLM_apply_apply
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow Space (s / 2))]
  simp only [sobolevBesselWeight, smul_eq_mul, Complex.real_smul]
  ring

/-- The actual weighted Fourier L² datum embeds as exactly the weighted
Fourier transform of the original Schwartz distribution. -/
theorem weightedFourierLp_toDistribution (s : ℝ) (φ : SchwartzMap Space ℂ) :
    (weightedFourierLp s φ : 𝓢'(Space, ℂ)) = weightedFourierDistribution s (φ : 𝓢'(Space, ℂ)) := by
  let ψ := SchwartzMap.smulLeftCLM ℂ (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) (𝓕 φ)
  change ((ψ.toLp 2 volume) : 𝓢'(Space, ℂ)) = _
  rw [Lp.toTemperedDistribution_toLp_eq]
  change (ψ : 𝓢'(Space, ℂ)) = sobolevWeightMultiplier s (𝓕 (φ : 𝓢'(Space, ℂ)))
  rw [TemperedDistribution.fourier_toTemperedDistributionCLM_eq, sobolevWeightMultiplier_schwartz]

/-- Reconstructing the concrete weighted Fourier datum returns the original
Schwartz distribution exactly. -/
theorem sobolevRealization_weightedFourierLp (s : ℝ) (φ : SchwartzMap Space ℂ) :
    sobolevRealization s (weightedFourierLp s φ) = (φ : 𝓢'(Space, ℂ)) := by
  rw [sobolevRealization_apply, weightedFourierLp_toDistribution, reconstruction_weightedFourier]

/-- The original compact smooth function is exactly the distribution realized
by its previously constructed Sobolev Hilbert vector. -/
theorem sobolevRealization_compactFourierLp (s : ℝ) (f : Space → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    sobolevRealization s (compactFourierLp s f hf hc) =
      ((NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc) : 𝓢'(Space, ℂ)) :=
  sobolevRealization_weightedFourierLp s _

/-- Explicit pairing with every Schwartz test: the realization acts by the
ordinary integral of the original physical function against that test. -/
theorem sobolevRealization_compactFourierLp_apply (s : ℝ) (f : Space → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ψ : SchwartzMap Space ℂ) :
    sobolevRealization s (compactFourierLp s f hf hc) ψ = ∫ x : Space, ψ x * f x := by
  rw [sobolevRealization_compactFourierLp, SchwartzMap.coe_apply]
  rfl

end NSFormalization.Paper3
