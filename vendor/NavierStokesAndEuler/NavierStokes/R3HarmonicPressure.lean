import NavierStokes.ComparatorR3Bridge
import Mathlib.Analysis.Distribution.Sobolev

/-!
# Removing a harmonic pressure-gradient ambiguity

The pressure-recovery step in the manuscript uses the fact that a harmonic
distribution lying in any `H^s(ℝ³)` is zero. Negative `s` is allowed. This
is stronger than an `L²` Liouville theorem and does not assume pointwise
bounds or decay of the pressure.
-/

noncomputable section

namespace NavierStokes.R3HarmonicPressure

open Set Filter MeasureTheory ProblemStatement TemperedDistribution FourierTransform
open scoped SchwartzMap Laplacian Topology

/-- A bounded smooth symbol with the same zero set as the Laplacian symbol. -/
def symbol (x : Space) : ℂ :=
  Complex.ofReal (‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ))

theorem symbol_temperate : symbol.HasTemperateGrowth := by
  unfold symbol
  fun_prop

theorem norm_symbol_le (x : Space) : ‖symbol x‖ ≤ 1 := by
  rw [symbol, Real.rpow_neg (by positivity)]
  norm_cast
  simp only [norm_mul, norm_pow, abs_norm, norm_inv, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), mul_inv_le_iff₀ (by positivity)]
  linarith [sq_nonneg ‖x‖]

theorem symbol_memLp : MemLp symbol ⊤ (volume : Measure Space) :=
  memLp_top_of_bound symbol_temperate.1.continuous.aestronglyMeasurable 1
    (Eventually.of_forall norm_symbol_le)

theorem symbol_ne_zero {x : Space} (hx : x ≠ 0) : symbol x ≠ 0 := by
  unfold symbol
  exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
    (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))

theorem multiplier_eq_zero_of_laplacian_eq_zero {f : 𝓢'(Space, ℂ)} (hf : Δ f = 0) :
    fourierMultiplierCLM ℂ symbol f = 0 := by
  have h := besselPotential_neg_two_laplacian_eq f
  rw [hf, map_zero] at h
  change 0 = -(2 * Real.pi) ^ 2 • fourierMultiplierCLM ℂ symbol f at h
  exact (smul_eq_zero.mp h.symm).resolve_left (by norm_num [Real.pi_ne_zero])

/-- A bounded multiplier which vanishes only at the origin is injective on
every `H^s`, since weighted Fourier transforms there are represented by `L²`
functions and a singleton has zero volume. -/
theorem eq_zero_of_multiplier_eq_zero {s : ℝ} {f : 𝓢'(Space, ℂ)}
    (hs : MemSobolev s 2 f) (hz : fourierMultiplierCLM ℂ symbol f = 0) : f = 0 := by
  obtain ⟨F, hF⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hs
  let M : Lp ℂ 2 (volume : Measure Space) := symbol_memLp.toLp symbol • F
  have hM : (M : 𝓢'(Space, ℂ)) = 0 := by
    rw [show (M : 𝓢'(Space, ℂ)) = smulLeftCLM ℂ symbol F from
      Lp.toTemperedDistribution_smul_eq symbol_temperate symbol_memLp F]
    rw [← hF, smulLeftCLM_smulLeftCLM_apply (by fun_prop) symbol_temperate]
    have heq := congrArg
      (fun h : 𝓢'(Space, ℂ) =>
        smulLeftCLM ℂ (fun x : Space => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 h)) hz
    rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq,
      smulLeftCLM_smulLeftCLM_apply symbol_temperate (by fun_prop),
      FourierTransform.fourier_zero, map_zero] at heq
    convert! heq using 1
    congr 2
    funext x
    exact mul_comm _ _
  have hMzero : M = 0 := by
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure Space)) (p := 2)))
    change (Lp.toTemperedDistributionCLM ℂ volume 2) M =
      (Lp.toTemperedDistributionCLM ℂ volume 2) 0
    rw [map_zero]
    exact hM
  have hFzero : F = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have hmae := Lp.eq_zero_iff_ae_eq_zero.mp hMzero
    filter_upwards [hmae, Lp.coeFn_lpSMul (r := 2) (symbol_memLp.toLp symbol) F,
      symbol_memLp.coeFn_toLp, ae_iff.mpr (show volume {x : Space | ¬ x ≠ 0} = 0 by simp)]
      with x hm hmul hsx hx
    change M x = 0 at hm
    change (symbol_memLp.toLp symbol • F : Lp ℂ 2 volume) x = _ at hmul
    rw [hmul] at hm
    change (symbol_memLp.toLp symbol) x • F x = 0 at hm
    rw [hsx] at hm
    exact (smul_eq_zero.mp hm).resolve_left (symbol_ne_zero hx)
  have hbf : besselPotential Space ℂ s f = 0 := by
    have hh : 𝓕 (besselPotential Space ℂ s f) = 0 := by
      rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply, hF, hFzero]
      change (Lp.toTemperedDistributionCLM ℂ volume 2) 0 = 0
      exact map_zero _
    have hi := congrArg (fun z : 𝓢'(Space, ℂ) => 𝓕⁻ z) hh
    simpa only [fourierInv_fourier_eq, FourierTransform.fourierInv_zero] using hi
  have hinv := congrArg (besselPotential Space ℂ (-s)) hbf
  simpa using hinv

/-- The harmonic Sobolev distribution needed when recovering the pressure
gradient from a finite-energy equation is zero, even at negative orders. -/
theorem eq_zero_of_harmonic_memSobolev {s : ℝ} {f : 𝓢'(Space, ℂ)}
    (hs : MemSobolev s 2 f) (hf : Δ f = 0) : f = 0 :=
  eq_zero_of_multiplier_eq_zero hs (multiplier_eq_zero_of_laplacian_eq_zero hf)

end NavierStokes.R3HarmonicPressure
