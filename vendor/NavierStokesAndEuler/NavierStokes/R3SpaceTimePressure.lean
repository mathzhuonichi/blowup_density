import NavierStokes.R3SpaceTimeHarmonic

/-!
# Spatial pressure on Euclidean space-time

The bounded spatial Riesz symbol acts on the Fourier transform of integrable
space-time stresses. Spatially harmonic ambiguities vanish in the Sobolev
class supplied by the finite-energy equation.
-/

noncomputable section
namespace NavierStokes.R3SpaceTimePressure

open Set Filter MeasureTheory TemperedDistribution FourierTransform R3SpaceTime
open scoped SchwartzMap Laplacian LineDeriv Topology ENNReal ContDiff

def rieszSymbol (i j : Fin 3) (z : Domain) : ℂ :=
  R3PressureFourier.rieszSymbol i j (spaceProj z)

theorem rieszSymbol_measurable (i j : Fin 3) : Measurable (rieszSymbol i j) :=
  (R3PressureFourier.rieszSymbol_measurable i j).comp spaceProj.continuous.measurable

theorem norm_rieszSymbol_le (i j : Fin 3) (z : Domain) : ‖rieszSymbol i j z‖ ≤ 1 :=
  R3PressureFourier.norm_rieszSymbol_le i j (spaceProj z)

theorem rieszSymbol_memLp (i j : Fin 3) : MemLp (rieszSymbol i j) ⊤ :=
  memLp_top_of_bound (rieszSymbol_measurable i j).aestronglyMeasurable 1
    (Eventually.of_forall (norm_rieszSymbol_le i j))

def rieszSymbolLp (i j : Fin 3) : Lp ℂ ⊤ (volume : Measure Domain) :=
  (rieszSymbol_memLp i j).toLp (rieszSymbol i j)

theorem rieszSymbolLp_ae (i j : Fin 3) :
    rieszSymbolLp i j =ᵐ[volume] rieszSymbol i j :=
  (rieszSymbol_memLp i j).coeFn_toLp

def frequencyL1 (f : Lp ℂ 1 (volume : Measure Domain)) : Lp ℂ ⊤ (volume : Measure Domain) :=
  (Real.Lp.fourierTransform f).memLp_top.toLp (Real.Lp.fourierTransform f)

theorem frequencyL1_ae (f : Lp ℂ 1 (volume : Measure Domain)) :
    frequencyL1 f =ᵐ[volume] 𝓕 (f : Domain → ℂ) :=
  (Real.Lp.fourierTransform f).memLp_top.coeFn_toLp

/-- The Fourier transform of an `L¹` distribution is its bounded classical
Fourier transform, regarded as an `L∞` distribution. -/
theorem fourier_L1 (f : Lp ℂ 1 (volume : Measure Domain)) :
    𝓕 (f : 𝓢'(Domain, ℂ)) = (frequencyL1 f : 𝓢'(Domain, ℂ)) := by
  ext φ
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply (μ := (volume : Measure Domain))]
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (f := (φ : Domain → ℂ)) (g := (f : Domain → ℂ))
    (μ := (volume : Measure Domain)) (ν := (volume : Measure Domain))
    (L := innerₗ Domain) Real.continuous_fourierChar continuous_inner φ.integrable
    (L1.integrable_coeFn f)
  calc
    _ = ∫ x : Domain, φ x • (𝓕 (f : Domain → ℂ)) x := by
      convert! hswap using 1
      congr 1
      funext x
      congr 1
      rw [Real.fourier_eq]
      unfold VectorFourier.fourierIntegral
      apply integral_congr_ae
      filter_upwards with y
      simp only [LinearMap.flip_apply, innerₗ_apply_apply, real_inner_comm]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [frequencyL1_ae f] with x hx
      rw [hx]

def pressureHat (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Domain)) :
    Lp ℂ ⊤ (volume : Measure Domain) := rieszSymbolLp i j • frequencyL1 f

/-- `R_i R_j f`, defined for arbitrary integrable data. -/
def pressureL1 (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Domain)) : 𝓢'(Domain, ℂ) :=
  𝓕⁻ (pressureHat i j f : 𝓢'(Domain, ℂ))

theorem pressureHat_ae (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Domain)) :
    pressureHat i j f =ᵐ[volume]
      fun x => rieszSymbol i j x * (𝓕 (f : Domain → ℂ)) x := by
  filter_upwards [Lp.coeFn_lpSMul (r := ⊤) (rieszSymbolLp i j) (frequencyL1 f),
    rieszSymbolLp_ae i j, frequencyL1_ae f] with x hm hs hf
  change pressureHat i j f x = _ at hm ⊢
  simpa only [Pi.smul_apply', smul_eq_mul, hs, hf] using hm

def sobolevWeight (x : Domain) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-2 : ℝ))

theorem sobolevWeight_temperate : sobolevWeight.HasTemperateGrowth := by
  unfold sobolevWeight
  fun_prop

theorem sobolevWeight_memLp : MemLp sobolevWeight 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    sobolevWeight_temperate.1.continuous.aestronglyMeasurable).mpr
  have hi : Integrable (fun x : Domain => (1 + ‖x‖ ^ 2) ^ (-4 : ℝ)) := by
    convert! (integrable_rpow_neg_one_add_norm_sq
      (μ := (volume : Measure Domain)) (r := 8) (by norm_num [finrank_domain])) using 1
    norm_num
  apply hi.congr
  filter_upwards with x
  have hwpos : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
  simp only [sobolevWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hwpos]
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num

/-- A bounded Fourier representative gives the required negative Sobolev
regularity. This avoids assigning a pointwise value to the pressure itself. -/
theorem inverse_fourier_memSobolev (F : Lp ℂ ⊤ (volume : Measure Domain)) :
    MemSobolev (-4) 2 (𝓕⁻ (F : 𝓢'(Domain, ℂ))) := by
  apply memSobolev_iff_exists_smulLeftCLM_fourier.mpr
  use (sobolevWeight_memLp.toLp sobolevWeight • F : Lp ℂ 2 volume)
  rw [fourier_fourierInv_eq]
  have he := Lp.toTemperedDistribution_smul_eq (p := 2) (q := ⊤) (r := 2)
    sobolevWeight_temperate sobolevWeight_memLp F
  have hw : (fun x : Domain => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((-4 : ℝ) / 2))) =
      sobolevWeight := by
    funext x
    simp only [sobolevWeight, show (-4 : ℝ) / 2 = -2 by norm_num]
  rw [hw]
  exact he.symm

theorem pressureL1_memSobolev (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Domain)) :
    MemSobolev (-4) 2 (pressureL1 i j f) :=
  inverse_fourier_memSobolev _

theorem lp_memSobolev (f : Lp ℂ 1 (volume : Measure Domain)) :
    MemSobolev (-4) 2 (f : 𝓢'(Domain, ℂ)) := by
  have hh := inverse_fourier_memSobolev (frequencyL1 f)
  rw [← fourier_L1, fourierInv_fourier_eq] at hh
  exact hh

theorem rieszSymbol_poisson (i j : Fin 3) (z : Domain) :
    laplacianSymbol z * rieszSymbol i j z = -(coordinateSymbol i z * coordinateSymbol j z) :=
  R3PressureFourier.rieszSymbol_poisson i j (spaceProj z)

theorem pressureHat_poisson (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Domain)) :
    smulLeftCLM ℂ laplacianSymbol (pressureHat i j f) =
      -smulLeftCLM ℂ (coordinateSymbol i * coordinateSymbol j) (frequencyL1 f) := by
  ext φ
  simp only [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, SchwartzMap.smulLeftCLM_apply_apply laplacianSymbol_temperate,
    SchwartzMap.smulLeftCLM_apply_apply
      ((coordinateSymbol_temperate i).mul (coordinateSymbol_temperate j))]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [pressureHat_ae i j f, frequencyL1_ae f] with x hp hf
  simp only [hp, hf, Pi.mul_apply, smul_eq_mul]
  have hsym := rieszSymbol_poisson i j x
  linear_combination φ x * (𝓕 (f : Domain → ℂ)) x * hsym

/-- The normalized pressure of an integrable stress component solves the
Poisson equation with its two distributional derivatives. -/
theorem pressureL1_poisson (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Domain)) :
    spatialLaplacian (pressureL1 i j f) = -∂_{spaceDirection i} (∂_{spaceDirection j}
      (f : 𝓢'(Domain, ℂ))) := by
  have he : 𝓕 (spatialLaplacian (pressureL1 i j f)) =
      𝓕 (-∂_{spaceDirection i} (∂_{spaceDirection j} (f : 𝓢'(Domain, ℂ)))) := by
    rw [fourier_spatialLaplacian, pressureL1, fourier_fourierInv_eq, pressureHat_poisson,
      FourierTransform.fourier_neg, fourier_second_derivative, fourier_L1]
    module
  have hi := congrArg (fun g : 𝓢'(Domain, ℂ) => 𝓕⁻ g) he
  simpa only [fourierInv_fourier_eq] using hi

def stressPressure (g : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain)) : 𝓢'(Domain, ℂ) :=
  ∑ i, ∑ j, pressureL1 i j (g i j)

theorem spatialLaplacian_finset_sum {ι : Type*} (s : Finset ι) (F : ι → 𝓢'(Domain, ℂ)) :
    spatialLaplacian (∑ i ∈ s, F i) = ∑ i ∈ s, spatialLaplacian (F i) := by
  simp only [spatialLaplacian, LineDeriv.lineDerivOp_sum]
  rw [Finset.sum_comm]

theorem memSobolev_finset_sum {ι : Type*} (s : Finset ι) {r : ℝ} (F : ι → 𝓢'(Domain, ℂ))
    (hF : ∀ i ∈ s, MemSobolev r 2 (F i)) : MemSobolev r 2 (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero Domain ℂ r 2
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- The pressure source for a complete integrable stress tensor. -/
theorem stressPressure_poisson (g : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain)) :
    spatialLaplacian (stressPressure g) =
      -(∑ i, ∑ j, ∂_{spaceDirection i} (∂_{spaceDirection j}
        (g i j : 𝓢'(Domain, ℂ)))) := by
  simp only [stressPressure, spatialLaplacian_finset_sum, pressureL1_poisson, Finset.sum_neg_distrib]

theorem stressPressure_memSobolev (g : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain)) :
    MemSobolev (-4) 2 (stressPressure g) := by
  apply memSobolev_finset_sum
  intro i _
  exact memSobolev_finset_sum _ _ (fun j _ => pressureL1_memSobolev i j (g i j))

theorem spatialLaplacian_lineDeriv (f : 𝓢'(Domain, ℂ)) (m : Domain) :
    spatialLaplacian (∂_{m} f) = ∂_{m} (spatialLaplacian f) := by
  have hm : (fun x : Domain => Complex.ofReal (inner ℝ x m)).HasTemperateGrowth := by fun_prop
  have he : 𝓕 (spatialLaplacian (∂_{m} f)) = 𝓕 (∂_{m} (spatialLaplacian f)) := by
    simp only [fourier_spatialLaplacian, fourier_lineDerivOp_eq, map_smul, smul_smul]
    rw [smulLeftCLM_smulLeftCLM_apply hm laplacianSymbol_temperate,
      smulLeftCLM_smulLeftCLM_apply laplacianSymbol_temperate hm,
      mul_comm laplacianSymbol (fun x : Domain => Complex.ofReal (inner ℝ x m))]
    module
  have hi := congrArg (fun g : 𝓢'(Domain, ℂ) => 𝓕⁻ g) he
  simpa only [fourierInv_fourier_eq] using hi

theorem eq_of_spatialLaplacian_eq {r : ℝ} {f g : 𝓢'(Domain, ℂ)}
    (hf : MemSobolev r 2 f) (hg : MemSobolev r 2 g)
    (he : spatialLaplacian f = spatialLaplacian g) : f = g := by
  apply sub_eq_zero.mp
  apply R3SpaceTimeHarmonic.eq_zero_of_spatially_harmonic_memSobolev (hf.sub hg)
  simp only [spatialLaplacian, sub_eq_add_neg, LineDeriv.lineDerivOp_add,
    LineDeriv.lineDerivOp_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  change spatialLaplacian f + -spatialLaplacian g = 0
  rw [he, add_neg_cancel]


/-- In the negative Sobolev class supplied by the finite-energy equation,
the pressure gradient is uniquely determined by the integrable stress. -/
theorem stressPressure_gradient_unique
    (g : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain)) (m : Domain)
    {P : 𝓢'(Domain, ℂ)} (hP : MemSobolev (-5) 2 P)
    (hsource : spatialLaplacian P = -∂_{m}
      (∑ i, ∑ j, ∂_{spaceDirection i} (∂_{spaceDirection j}
        (g i j : 𝓢'(Domain, ℂ))))) :
    P = ∂_{m} (stressPressure g) := by
  apply eq_of_spatialLaplacian_eq hP
  · convert! (stressPressure_memSobolev g).lineDerivOp (m := m) using 1
    norm_num
  · rw [spatialLaplacian_lineDeriv, stressPressure_poisson, LineDeriv.lineDerivOp_neg]
    exact hsource

end NavierStokes.R3SpaceTimePressure
