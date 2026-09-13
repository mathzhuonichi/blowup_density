import NavierStokes.R3SpaceTime

/-!
# Spatially harmonic Sobolev distributions on space-time vanish

Only the three spatial derivatives enter the harmonicity condition. The
weighted Fourier representative is an `L²` function on four-dimensional
space-time; the exceptional frequency line has Lebesgue measure zero.
-/

noncomputable section
namespace NavierStokes.R3SpaceTimeHarmonic

open Set Filter MeasureTheory TemperedDistribution FourierTransform R3SpaceTime
open scoped SchwartzMap Topology

def symbol (z : Domain) : ℂ :=
  Complex.ofReal (‖spaceProj z‖ ^ 2 * (1 + ‖z‖ ^ 2) ^ (-1 : ℝ))

theorem symbol_temperate : symbol.HasTemperateGrowth := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp
    (((Function.hasTemperateGrowth_norm_sq ProblemStatement.Space).comp spaceProj.hasTemperateGrowth).mul
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow Domain (-1)))

theorem norm_symbol_le (z : Domain) : ‖symbol z‖ ≤ 1 := by
  rw [symbol, Real.rpow_neg (by positivity)]
  norm_cast
  simp only [norm_mul, norm_pow, abs_norm, norm_inv, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), mul_inv_le_iff₀ (by positivity)]
  nlinarith [norm_spaceProj_le z, norm_nonneg (spaceProj z), norm_nonneg z]

theorem symbol_memLp : MemLp symbol ⊤ (volume : Measure Domain) :=
  memLp_top_of_bound symbol_temperate.1.continuous.aestronglyMeasurable 1
    (Eventually.of_forall norm_symbol_le)

theorem symbol_ne_zero {z : Domain} (hz : spaceProj z ≠ 0) : symbol z ≠ 0 := by
  unfold symbol
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
    (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))

theorem multiplier_eq_zero_of_spatialLaplacian_eq_zero {f : 𝓢'(Domain, ℂ)}
    (hf : spatialLaplacian f = 0) : fourierMultiplierCLM ℂ symbol f = 0 := by
  have hh := fourier_spatialLaplacian f
  rw [hf, FourierTransform.fourier_zero] at hh
  have hzero : smulLeftCLM ℂ laplacianSymbol (𝓕 f) = 0 :=
    (smul_eq_zero.mp hh.symm).resolve_left (by norm_num [Real.pi_ne_zero])
  let w : Domain → ℂ := fun z => Complex.ofReal ((1 + ‖z‖ ^ 2) ^ (-1 : ℝ))
  have hw : w.HasTemperateGrowth := by unfold w; fun_prop
  have he : laplacianSymbol * w = symbol := by
    funext z
    simp only [Pi.mul_apply, laplacianSymbol, w, symbol, Complex.ofReal_mul]
  have hz := congrArg (smulLeftCLM ℂ w) hzero
  rw [smulLeftCLM_smulLeftCLM_apply laplacianSymbol_temperate hw, he, map_zero] at hz
  rw [fourierMultiplierCLM_apply, hz, FourierTransform.fourierInv_zero]

theorem eq_zero_of_multiplier_eq_zero {s : ℝ} {f : 𝓢'(Domain, ℂ)}
    (hs : MemSobolev s 2 f) (hz : fourierMultiplierCLM ℂ symbol f = 0) : f = 0 := by
  obtain ⟨F, hF⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hs
  let M : Lp ℂ 2 (volume : Measure Domain) := symbol_memLp.toLp symbol • F
  have hM : (M : 𝓢'(Domain, ℂ)) = 0 := by
    rw [show (M : 𝓢'(Domain, ℂ)) = smulLeftCLM ℂ symbol F from
      Lp.toTemperedDistribution_smul_eq symbol_temperate symbol_memLp F]
    rw [← hF, smulLeftCLM_smulLeftCLM_apply (by fun_prop) symbol_temperate]
    have heq := congrArg
      (fun h : 𝓢'(Domain, ℂ) =>
        smulLeftCLM ℂ (fun z : Domain => ((1 + ‖z‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 h)) hz
    rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq,
      smulLeftCLM_smulLeftCLM_apply symbol_temperate (by fun_prop),
      FourierTransform.fourier_zero, map_zero] at heq
    convert! heq using 1
    congr 2
    funext z
    exact mul_comm _ _
  have hMzero : M = 0 := by
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure Domain)) (p := 2)))
    change (Lp.toTemperedDistributionCLM ℂ volume 2) M =
      (Lp.toTemperedDistributionCLM ℂ volume 2) 0
    rw [map_zero]
    exact hM
  have hFzero : F = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have hmae := Lp.eq_zero_iff_ae_eq_zero.mp hMzero
    have hline : ∀ᵐ z ∂volume, spaceProj z ≠ 0 := by
      apply ae_iff.mpr
      simpa only [not_not] using volume_spatial_zero
    filter_upwards [hmae, Lp.coeFn_lpSMul (r := 2) (symbol_memLp.toLp symbol) F,
      symbol_memLp.coeFn_toLp, hline] with z hm hmul hsz hz
    change M z = 0 at hm
    change (symbol_memLp.toLp symbol • F : Lp ℂ 2 volume) z = _ at hmul
    rw [hmul] at hm
    change (symbol_memLp.toLp symbol) z • F z = 0 at hm
    rw [hsz] at hm
    exact (smul_eq_zero.mp hm).resolve_left (symbol_ne_zero hz)
  have hbf : besselPotential Domain ℂ s f = 0 := by
    have hh : 𝓕 (besselPotential Domain ℂ s f) = 0 := by
      rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply, hF, hFzero]
      change (Lp.toTemperedDistributionCLM ℂ volume 2) 0 = 0
      exact map_zero _
    have hi := congrArg (fun z : 𝓢'(Domain, ℂ) => 𝓕⁻ z) hh
    simpa only [fourierInv_fourier_eq, FourierTransform.fourierInv_zero] using hi
  have hinv := congrArg (besselPotential Domain ℂ (-s)) hbf
  simpa using hinv

/-- No spatially harmonic ambiguity survives the negative Sobolev class
obtained from the finite-energy space-time equation. -/
theorem eq_zero_of_spatially_harmonic_memSobolev {s : ℝ} {f : 𝓢'(Domain, ℂ)}
    (hs : MemSobolev s 2 f) (hf : spatialLaplacian f = 0) : f = 0 :=
  eq_zero_of_multiplier_eq_zero hs (multiplier_eq_zero_of_spatialLaplacian_eq_zero hf)

end NavierStokes.R3SpaceTimeHarmonic
