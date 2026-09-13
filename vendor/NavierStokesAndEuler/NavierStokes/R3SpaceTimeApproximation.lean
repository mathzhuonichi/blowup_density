import NavierStokes.R3SpatialConvolution
import NavierStokes.R3SpaceTimePressure

/-!
# Spatial Gaussian regularizers converge on space-time

The actual spatial convolutions converge to the normalized space-time
pressure distribution. This permits using slice-wise weighted estimates
without requiring the pressure to be square-integrable in time.
-/

noncomputable section
namespace NavierStokes.R3SpaceTimeApproximation

open Set Filter MeasureTheory FourierTransform TemperedDistribution
open R3SpaceTime R3SpaceTimePressure R3RieszKernel R3SpatialConvolution
open scoped Topology ENNReal SchwartzMap

def multiplier (n : ℕ) (i j : Fin 3) (z : Domain) : ℂ :=
  𝓕 (truncatedKernel n i j) (spaceProj z)

theorem symbol_memLp (n : ℕ) (i j : Fin 3) : MemLp (multiplier n i j) ⊤ :=
  memLp_top_of_bound
    ((R3RieszApproximation.classical_fourier_continuous (truncatedKernel_integrable n i j)).comp
      spaceProj.continuous).aestronglyMeasurable 1
    (Eventually.of_forall fun z => norm_fourier_truncatedKernel_le n i j (spaceProj z))

def symbolLp (n : ℕ) (i j : Fin 3) : Lp ℂ ⊤ (volume : Measure Domain) :=
  (symbol_memLp n i j).toLp (multiplier n i j)

theorem symbolLp_ae (n : ℕ) (i j : Fin 3) :
    symbolLp n i j =ᵐ[volume] multiplier n i j := (symbol_memLp n i j).coeFn_toLp

def operatorL1 (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Domain)) : 𝓢'(Domain, ℂ) :=
  𝓕⁻ ((symbolLp n i j • frequencyL1 g : Lp ℂ ⊤ volume) : 𝓢'(Domain, ℂ))

theorem regularized_memLp_one (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Domain)) :
    MemLp (regularized n i j g) 1 :=
  memLp_one_iff_integrable.mpr (regularized_integrable n i j (L1.integrable_coeFn g))

def regularizedLp (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Domain)) : Lp ℂ 1 (volume : Measure Domain) :=
  (regularized_memLp_one n i j g).toLp (regularized n i j g)

theorem regularizedLp_ae (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Domain)) :
    regularizedLp n i j g =ᵐ[volume] regularized n i j g :=
  (regularized_memLp_one n i j g).coeFn_toLp

/-- The Fourier regularization is the distribution of the actual
integrable convolution with its Gaussian kernel. -/
theorem operatorL1_eq_regularizedLp (n : ℕ) (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Domain)) :
    operatorL1 n i j g = (regularizedLp n i j g : 𝓢'(Domain, ℂ)) := by
  have he : frequencyL1 (regularizedLp n i j g) = symbolLp n i j • frequencyL1 g := by
    apply Lp.ext
    filter_upwards [frequencyL1_ae (regularizedLp n i j g),
      Lp.coeFn_lpSMul (r := ⊤) (symbolLp n i j) (frequencyL1 g), symbolLp_ae n i j,
      frequencyL1_ae g] with x hx hm hs hg
    rw [hx, Real.fourier_congr_ae (regularizedLp_ae n i j g) x,
      regularized_fourier n i j (L1.integrable_coeFn g), hm]
    simp only [Pi.smul_apply', smul_eq_mul, hs, hg, multiplier]
  rw [operatorL1, ← he, ← fourier_L1, fourierInv_fourier_eq]

/-- Pointwise convergence of uniformly bounded Fourier representatives
implies convergence of their tempered distributions. -/
theorem distribution_tendsto_of_bounded {F : ℕ → Lp ℂ ⊤ (volume : Measure Domain)}
    {f : Lp ℂ ⊤ (volume : Measure Domain)} {M : ℝ}
    (hF : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ M)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => (F n : 𝓢'(Domain, ℂ))) atTop (𝓝 (f : 𝓢'(Domain, ℂ))) := by
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

theorem norm_classical_fourier_le (g : Lp ℂ 1 (volume : Measure Domain)) (x : Domain) :
    ‖𝓕 (g : Domain → ℂ) x‖ ≤ ‖g‖ := by
  rw [Real.fourier_eq]
  apply (norm_integral_le_integral_norm _).trans
  simp only [Circle.norm_smul]
  exact (L1.norm_eq_integral_norm g).symm.le

theorem operatorL1_tendsto (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Domain)) :
    Tendsto (fun n => operatorL1 n i j g) atTop (𝓝 (pressureL1 i j g)) := by
  let F (n : ℕ) : Lp ℂ ⊤ (volume : Measure Domain) := symbolLp n i j • frequencyL1 g
  have hrep (n : ℕ) : F n =ᵐ[volume]
      fun x => 𝓕 (truncatedKernel n i j) (spaceProj x) * 𝓕 (g : Domain → ℂ) x := by
    filter_upwards [Lp.coeFn_lpSMul (r := ⊤) (symbolLp n i j) (frequencyL1 g),
      symbolLp_ae n i j, frequencyL1_ae g] with x hm hs hg
    change F n x = _ at hm ⊢
    simpa only [Pi.smul_apply', smul_eq_mul, hs, hg, multiplier] using hm
  have hb (n : ℕ) : ∀ᵐ x ∂volume, ‖F n x‖ ≤ ‖g‖ := by
    filter_upwards [hrep n] with x hx
    rw [hx, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_fourier_truncatedKernel_le n i j (spaceProj x))).trans
      (norm_classical_fourier_le g x)
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (pressureHat i j g x)) := by
    filter_upwards [(ae_all_iff.mpr hrep), pressureHat_ae i j g] with x hx h0
    simpa only [hx, h0, rieszSymbol] using (fourier_truncatedKernel_tendsto i j (spaceProj x)).mul_const (𝓕 (g : Domain → ℂ) x)
  have hh := distribution_tendsto_of_bounded hb hlim
  simpa only [Function.comp_def, operatorL1, pressureL1, F] using
    (continuous_fourierInv.tendsto (pressureHat i j g : 𝓢'(Domain, ℂ))).comp hh

theorem regularized_tendsto (i j : Fin 3) (g : Lp ℂ 1 (volume : Measure Domain)) :
    Tendsto (fun n => (regularizedLp n i j g : 𝓢'(Domain, ℂ))) atTop
      (𝓝 (pressureL1 i j g)) := by
  simpa only [operatorL1_eq_regularizedLp] using operatorL1_tendsto i j g

/-- The convergence applies to the actual input function, independently of
which representative Mathlib chooses for its `Lp` class. -/
theorem actual_regularized_distribution (n : ℕ) (i j : Fin 3) {g : Domain → ℂ}
    (hg : MemLp g 1) :
    let hn : MemLp (regularized n i j g) 1 :=
      memLp_one_iff_integrable.mpr (regularized_integrable n i j (memLp_one_iff_integrable.mp hg))
    operatorL1 n i j (hg.toLp g) = (hn.toLp (regularized n i j g) : 𝓢'(Domain, ℂ)) := by
  intro hn
  have he : frequencyL1 (hn.toLp (regularized n i j g)) = symbolLp n i j • frequencyL1 (hg.toLp g) := by
    apply Lp.ext
    filter_upwards [frequencyL1_ae (hn.toLp (regularized n i j g)),
      Lp.coeFn_lpSMul (r := ⊤) (symbolLp n i j) (frequencyL1 (hg.toLp g)), symbolLp_ae n i j,
      frequencyL1_ae (hg.toLp g)] with x hx hm hs hfreq
    rw [hx, Real.fourier_congr_ae hn.coeFn_toLp x,
      regularized_fourier n i j (memLp_one_iff_integrable.mp hg), hm]
    simp only [Pi.smul_apply', smul_eq_mul, hs, hfreq, multiplier,
      Real.fourier_congr_ae hg.coeFn_toLp x]
  rw [operatorL1, ← he, ← fourier_L1, fourierInv_fourier_eq]

theorem actual_regularized_test_tendsto (i j : Fin 3) {g : Domain → ℂ}
    (hg : MemLp g 1) (φ : 𝓢(Domain, ℂ)) :
    Tendsto (fun n => ∫ z : Domain, φ z * regularized n i j g z) atTop
      (𝓝 (pressureL1 i j (hg.toLp g) φ)) := by
  have hh := (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp
    (operatorL1_tendsto i j (hg.toLp g))) φ
  apply hh.congr'
  filter_upwards with n
  rw [actual_regularized_distribution n i j hg, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.mpr (regularized_integrable n i j (memLp_one_iff_integrable.mp hg))).coeFn_toLp]
    with z hz
  simp only [hz, smul_eq_mul]

end NavierStokes.R3SpaceTimeApproximation
