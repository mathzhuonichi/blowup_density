import NSFormalization.Paper3.CompactSobolevRealization
import NavierStokes.R3.SchwartzCompactApproximation

/-!
# Schwartz density in the actual Sobolev Hilbert norm

Every Schwartz Fourier datum has a Schwartz inverse weighted Fourier preimage.
Consequently the original Schwartz functions are dense in the full Sobolev
Hilbert model, for every real order. The existing source-library physical
cutoff approximation then gives density of physical compact smooth functions.
No new cutoff estimates or abstract compactness assumptions are introduced.
-/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff ENNReal SchwartzMap

/-- Inverse weighted Fourier transform on Schwartz functions. -/
def inverseWeightedSchwartz (s : ℝ) (ψ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ
    (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) ψ)

 theorem weightedFourierLp_inverseWeightedSchwartz (s : ℝ) (ψ : SchwartzMap Space ℂ) :
    weightedFourierLp s (inverseWeightedSchwartz s ψ) = ψ.toLp 2 volume := by
  have heq : SchwartzMap.smulLeftCLM ℂ
      (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2))
      (𝓕 (inverseWeightedSchwartz s ψ)) = ψ := by
    unfold inverseWeightedSchwartz
    rw [fourier_fourierInv_eq]
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow Space (s / 2)),
      SchwartzMap.smulLeftCLM_apply_apply
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow Space (-s / 2)), smul_smul,
      ← Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖ ^ 2)]
    simp [show s / 2 + -s / 2 = 0 by ring]
  change (SchwartzMap.smulLeftCLM ℂ
      (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2))
      (𝓕 (inverseWeightedSchwartz s ψ))).toLp 2 volume = _
  rw [heq]

/-- Density in the full Hilbert norm, including negative and noninteger orders. -/
theorem denseRange_weightedFourierLp (s : ℝ) : DenseRange (weightedFourierLp s) := by
  intro h
  apply closure_mono (s := Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure Space))) ?_
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top h)
  rintro _ ⟨ψ, rfl⟩
  exact ⟨inverseWeightedSchwartz s ψ, weightedFourierLp_inverseWeightedSchwartz s ψ⟩

/-- The source library's physical spatial cutoffs converge in every Sobolev order. -/
theorem weightedFourierLp_physicalCutoff_tendsto (s : ℝ) (ψ : SchwartzMap Space ℂ) :
    Filter.Tendsto (fun n => weightedFourierLp s
      (NavierStokesR3.SchwartzCompactApproximation.approximate ψ n))
      Filter.atTop (nhds (weightedFourierLp s ψ)) :=
  ((weightedFourierLp s).continuous.tendsto ψ).comp
    (NavierStokesR3.SchwartzCompactApproximation.tendsto_approximate ψ)

/-- Physical compact smooth functions are dense in the complete Sobolev Hilbert norm. -/
theorem dense_compact_weightedFourierLp (s : ℝ) :
    Dense ((weightedFourierLp s) ''
      {ψ : SchwartzMap Space ℂ | HasCompactSupport (ψ : Space → ℂ)}) :=
  (denseRange_weightedFourierLp s).dense_image (weightedFourierLp s).continuous
    NavierStokesR3.SchwartzCompactApproximation.dense_hasCompactSupport

end NSFormalization.Paper3
