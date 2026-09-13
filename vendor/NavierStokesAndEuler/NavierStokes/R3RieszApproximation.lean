import NavierStokes.R3RieszKernel
import Mathlib.Analysis.Fourier.Convolution

/-!
# Convergence of the Gaussian regularizations of pressure

The finite-scale kernels act by ordinary absolutely convergent convolution.
Their operators converge in tempered distributions on `L¹` inputs and
strongly in `L²` on `L²` inputs.
-/

noncomputable section
namespace NavierStokes.R3RieszApproximation

open Set Filter MeasureTheory ProblemStatement FourierTransform TemperedDistribution
open R3PressureFourier R3RieszKernel R3ConvolutionYoung R3PressureCommutator
open scoped Topology ENNReal SchwartzMap

theorem classical_fourier_continuous {g : Space → ℂ} (hg : Integrable g) : Continuous (𝓕 g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hg

def regularized (n : ℕ) (i j : Fin 3) (g : Space → ℂ) : Space → ℂ :=
  scalarConvolution (truncatedKernel n i j) g

theorem regularized_integrable (n : ℕ) (i j : Fin 3) {g : Space → ℂ} (hg : Integrable g) :
    Integrable (regularized n i j g) :=
  (truncatedKernel_integrable n i j).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

theorem regularized_ae_integrable (n : ℕ) (i j : Fin 3) {g : Space → ℂ} (hg : Integrable g) :
    ∀ᵐ x ∂volume, Integrable (fun y : Space => truncatedKernel n i j y * g (x - y)) :=
  (truncatedKernel_integrable n i j).ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hg

theorem regularized_fourier (n : ℕ) (i j : Fin 3) {g : Space → ℂ} (hg : Integrable g) (ξ : Space) :
    𝓕 (regularized n i j g) ξ = 𝓕 (truncatedKernel n i j) ξ * 𝓕 g ξ :=
  Real.fourier_mul_convolution_eq (truncatedKernel_integrable n i j) hg ξ

theorem symbol_memLp (n : ℕ) (i j : Fin 3) : MemLp (𝓕 (truncatedKernel n i j)) ⊤ :=
  memLp_top_of_bound (classical_fourier_continuous (truncatedKernel_integrable n i j)).aestronglyMeasurable 1
    (Eventually.of_forall (norm_fourier_truncatedKernel_le n i j))

def symbolLp (n : ℕ) (i j : Fin 3) : Lp ℂ ⊤ (volume : Measure Space) :=
  (symbol_memLp n i j).toLp (𝓕 (truncatedKernel n i j))

theorem symbolLp_ae (n : ℕ) (i j : Fin 3) :
    symbolLp n i j =ᵐ[volume] 𝓕 (truncatedKernel n i j) := (symbol_memLp n i j).coeFn_toLp

def operatorL1 (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space)) : 𝓢'(Space, ℂ) :=
  𝓕⁻ ((symbolLp n i j • frequencyL1 g : Lp ℂ ⊤ volume) : 𝓢'(Space, ℂ))

def operatorL2 (n : ℕ) (i j : Fin 3) (g : Lp ℂ 2 (volume : Measure Space)) : Lp ℂ 2 (volume : Measure Space) :=
  𝓕⁻ (symbolLp n i j • 𝓕 g)

theorem regularized_memLp_one (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space)) :
    MemLp (regularized n i j g) 1 :=
  memLp_one_iff_integrable.mpr (regularized_integrable n i j (L1.integrable_coeFn g))

def regularizedLp (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space)) : Lp ℂ 1 (volume : Measure Space) :=
  (regularized_memLp_one n i j g).toLp (regularized n i j g)

theorem regularizedLp_ae (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space)) :
    regularizedLp n i j g =ᵐ[volume] regularized n i j g :=
  (regularized_memLp_one n i j g).coeFn_toLp

/-- The Fourier regularization is the distribution of the actual
integrable convolution with its Gaussian kernel. -/
theorem operatorL1_eq_regularizedLp (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space)) :
    operatorL1 n i j g = (regularizedLp n i j g : 𝓢'(Space, ℂ)) := by
  have he : frequencyL1 (regularizedLp n i j g) = symbolLp n i j • frequencyL1 g := by
    apply Lp.ext
    filter_upwards [frequencyL1_ae (regularizedLp n i j g),
      Lp.coeFn_lpSMul (r := ⊤) (symbolLp n i j) (frequencyL1 g), symbolLp_ae n i j,
      frequencyL1_ae g] with x hx hm hs hg
    rw [hx, Real.fourier_congr_ae (regularizedLp_ae n i j g) x,
      regularized_fourier n i j (L1.integrable_coeFn g), hm]
    simp only [Pi.smul_apply', smul_eq_mul, hs, hg]
  rw [operatorL1, ← he, ← fourier_L1, fourierInv_fourier_eq]

theorem operatorL1_eq_operatorL2 (n : ℕ) (i j : Fin 3)
    {f : Lp ℂ 1 (volume : Measure Space)} {g : Lp ℂ 2 (volume : Measure Space)}
    (h : (f : Space → ℂ) =ᵐ[volume] g) :
    operatorL1 n i j f = (operatorL2 n i j g : 𝓢'(Space, ℂ)) := by
  have hfreq : (frequencyL1 f : 𝓢'(Space, ℂ)) = (𝓕 g : Lp ℂ 2 volume) := by
    rw [← fourier_L1, ← Lp.fourier_toTemperedDistribution_eq, lp_distribution_eq_of_ae h]
  have hfreqae := lp_ae_of_distribution_eq hfreq
  have hprod : (symbolLp n i j • frequencyL1 f : Lp ℂ ⊤ volume) =ᵐ[volume]
      (symbolLp n i j • 𝓕 g : Lp ℂ 2 volume) := by
    filter_upwards [Lp.coeFn_lpSMul (r := ⊤) (symbolLp n i j) (frequencyL1 f),
      Lp.coeFn_lpSMul (r := 2) (symbolLp n i j) (𝓕 g), hfreqae] with x hl hr he
    rw [hl, hr]
    simp only [Pi.smul_apply', he]
  rw [operatorL1, lp_distribution_eq_of_ae hprod, Lp.fourierInv_toTemperedDistribution_eq]
  rfl

/-- Pointwise convergence of uniformly bounded Fourier representatives
implies convergence of their tempered distributions. -/
theorem distribution_tendsto_of_bounded {F : ℕ → Lp ℂ ⊤ (volume : Measure Space)}
    {f : Lp ℂ ⊤ (volume : Measure Space)} {M : ℝ}
    (hF : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ M)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (F n : 𝓢'(Space, ℂ))) atTop (𝓝 (f : 𝓢'(Space, ℂ))) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro φ
  simp only [Lp.toTemperedDistribution_apply]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖ * M)
  · intro n
    exact φ.continuous.aestronglyMeasurable.smul (Lp.memLp (F n)).1
  · exact φ.integrable.norm.mul_const M
  · intro n
    filter_upwards [hF n] with x hx
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.smul hx

theorem operatorL1_tendsto (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Space)) :
    Tendsto (fun n => operatorL1 n i j g) atTop (𝓝 (pressureL1 i j g)) := by
  let F (n : ℕ) : Lp ℂ ⊤ (volume : Measure Space) := symbolLp n i j • frequencyL1 g
  have hrep (n : ℕ) : F n =ᵐ[volume]
      fun x => 𝓕 (truncatedKernel n i j) x * 𝓕 (g : Space → ℂ) x := by
    filter_upwards [Lp.coeFn_lpSMul (r := ⊤) (symbolLp n i j) (frequencyL1 g),
      symbolLp_ae n i j, frequencyL1_ae g] with x hm hs hg
    change F n x = _ at hm ⊢
    simpa only [Pi.smul_apply', smul_eq_mul, hs, hg] using hm
  have hb (n : ℕ) : ∀ᵐ x ∂volume, ‖F n x‖ ≤ ‖g‖ := by
    filter_upwards [hrep n] with x hx
    rw [hx, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_fourier_truncatedKernel_le n i j x)).trans
      (norm_classical_fourier_le g x)
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (pressureHat i j g x)) := by
    filter_upwards [(ae_all_iff.mpr hrep), pressureHat_ae i j g] with x hx h0
    simpa only [hx, h0] using (fourier_truncatedKernel_tendsto i j x).mul_const (𝓕 (g : Space → ℂ) x)
  have hh := distribution_tendsto_of_bounded hb hlim
  simpa only [Function.comp_def, operatorL1, pressureL1, F] using
    (continuous_fourierInv.tendsto (pressureHat i j g : 𝓢'(Space, ℂ))).comp hh

/-- Convert the concrete `lpNorm` convergence estimate into convergence in
Mathlib's complete `Lp` space. -/
theorem tendsto_Lp_two_of_lpNorm {F : ℕ → Lp ℂ 2 (volume : Measure Space)}
    {f : Lp ℂ 2 (volume : Measure Space)}
    (h : Tendsto (fun n => lpNorm (fun x => F n x - f x) 2 volume) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (n : ℕ) : ‖F n - f‖ = lpNorm (fun x => F n x - f x) 2 volume := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub (F n) f),
      toReal_eLpNorm ((Lp.memLp (F n)).1.sub (Lp.memLp f).1)]
    rfl
  simpa only [he] using h

theorem operatorL2_tendsto (i j : Fin 3) (g : Lp ℂ 2 (volume : Measure Space)) :
    Tendsto (fun n => operatorL2 n i j g) atTop (𝓝 (pressureL2 i j g)) := by
  let F (n : ℕ) : Lp ℂ 2 (volume : Measure Space) := symbolLp n i j • 𝓕 g
  let f : Lp ℂ 2 (volume : Measure Space) := rieszSymbolLp i j • 𝓕 g
  have hrep (n : ℕ) : F n =ᵐ[volume]
      fun x => 𝓕 (truncatedKernel n i j) x * (𝓕 g : Lp ℂ 2 volume) x := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (symbolLp n i j) (𝓕 g), symbolLp_ae n i j] with x hm hs
    change F n x = _ at hm ⊢
    simpa only [Pi.smul_apply', smul_eq_mul, hs] using hm
  have hrep₀ : f =ᵐ[volume] fun x => rieszSymbol i j x * (𝓕 g : Lp ℂ 2 volume) x := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (rieszSymbolLp i j) (𝓕 g), rieszSymbolLp_ae i j] with x hm hs
    change f x = _ at hm ⊢
    simpa only [Pi.smul_apply', smul_eq_mul, hs] using hm
  have hb (n : ℕ) : ∀ᵐ x ∂volume, ‖F n x‖ ≤ ‖(𝓕 g : Lp ℂ 2 volume) x‖ := by
    filter_upwards [hrep n] with x hx
    rw [hx, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_fourier_truncatedKernel_le n i j x)
  have hb₀ : ∀ᵐ x ∂volume, ‖f x‖ ≤ ‖(𝓕 g : Lp ℂ 2 volume) x‖ := by
    filter_upwards [hrep₀] with x hx
    rw [hx, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_rieszSymbol_le i j x)
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    filter_upwards [ae_all_iff.mpr hrep, hrep₀] with x hx h0
    simpa only [hx, h0] using
      (fourier_truncatedKernel_tendsto i j x).mul_const ((𝓕 g : Lp ℂ 2 volume) x)
  have hh := tendsto_lpNorm_two_of_dominated (fun n => (Lp.memLp (F n)).1) (Lp.memLp f).1
    (Lp.memLp (𝓕 g : Lp ℂ 2 volume)).norm hb hb₀ hlim
  have hh' := tendsto_Lp_two_of_lpNorm hh
  simpa only [Function.comp_def, operatorL2, pressureL2, F, f] using
    (continuous_fourierInv.tendsto f).comp hh'


theorem regularized_congr_ae (n : ℕ) (i j : Fin 3) {f g : Space → ℂ} (h : f =ᵐ[volume] g) :
    regularized n i j f = regularized n i j g :=
  convolution_congr (ContinuousLinearMap.mul ℂ ℂ) EventuallyEq.rfl h

theorem tendsto_toLp_two_of_lpNorm {F : ℕ → Space → ℂ} {f : Space → ℂ}
    (hF : ∀ n, MemLp (F n) 2) (hf : MemLp f 2)
    (h : Tendsto (fun n => lpNorm (F n - f) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f hf).mpr
  have hh := (ENNReal.continuous_ofReal.tendsto 0).comp h
  simpa only [Function.comp_def, ofReal_lpNorm ((hF _).sub hf), ENNReal.ofReal_zero] using hh


theorem norm_operatorL2_le (n : ℕ) (i j : Fin 3) (g : Lp ℂ 2 (volume : Measure Space)) :
    ‖operatorL2 n i j g‖ ≤ ‖g‖ := by
  have hnorm (f : Lp ℂ 2 (volume : Measure Space)) : ‖𝓕⁻ f‖ = ‖f‖ :=
    (Lp.fourierTransformₗᵢ Space ℂ).symm.norm_map f
  rw [operatorL2, hnorm, ← Lp.norm_fourier_eq g]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (symbolLp n i j) (𝓕 g), symbolLp_ae n i j] with x hm hs
  rw [hm]
  change ‖symbolLp n i j x • (𝓕 g : Lp ℂ 2 volume) x‖ ≤ ‖(𝓕 g : Lp ℂ 2 volume) x‖
  rw [hs, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_fourier_truncatedKernel_le n i j x)

end NavierStokes.R3RieszApproximation
