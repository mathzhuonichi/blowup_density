import NavierStokes.R3HarmonicPressure

/-!
# The normalized whole-space pressure operator

The second-order Riesz symbol is bounded but is not smooth at the origin.
It is therefore multiplied with actual `Lp` functions here, rather than
passed to the smooth-symbol multiplier on arbitrary tempered distributions.
For `L¹` data its bounded Fourier transform gives a tempered distribution;
for `L²` data Plancherel gives a bounded operator.
-/

noncomputable section

namespace NavierStokes.R3PressureFourier

open Set Filter MeasureTheory ProblemStatement TemperedDistribution FourierTransform
open scoped SchwartzMap Laplacian LineDeriv Topology ENNReal
open scoped ContDiff BoundedContinuousFunction

def rieszSymbol (i j : Fin 3) (x : Space) : ℂ :=
  Complex.ofReal (-(x i * x j) / ‖x‖ ^ 2)

theorem rieszSymbol_measurable (i j : Fin 3) : Measurable (rieszSymbol i j) := by
  unfold rieszSymbol
  fun_prop

theorem norm_rieszSymbol_le (i j : Fin 3) (x : Space) : ‖rieszSymbol i j x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [rieszSymbol, hx]
  have hi : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  have hj : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
  have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  simp only [rieszSymbol, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_neg, abs_mul, abs_pow, abs_norm]
  rw [div_le_one hn]
  nlinarith [mul_le_mul hi hj (abs_nonneg (x j)) (norm_nonneg x)]

theorem rieszSymbol_memLp (i j : Fin 3) : MemLp (rieszSymbol i j) ⊤ :=
  memLp_top_of_bound (rieszSymbol_measurable i j).aestronglyMeasurable 1
    (Eventually.of_forall (norm_rieszSymbol_le i j))

def rieszSymbolLp (i j : Fin 3) : Lp ℂ ⊤ (volume : Measure Space) :=
  (rieszSymbol_memLp i j).toLp (rieszSymbol i j)

theorem rieszSymbolLp_ae (i j : Fin 3) :
    rieszSymbolLp i j =ᵐ[volume] rieszSymbol i j :=
  (rieszSymbol_memLp i j).coeFn_toLp

def frequencyL1 (f : Lp ℂ 1 (volume : Measure Space)) : Lp ℂ ⊤ (volume : Measure Space) :=
  (Real.Lp.fourierTransform f).memLp_top.toLp (Real.Lp.fourierTransform f)

theorem frequencyL1_ae (f : Lp ℂ 1 (volume : Measure Space)) :
    frequencyL1 f =ᵐ[volume] 𝓕 (f : Space → ℂ) :=
  (Real.Lp.fourierTransform f).memLp_top.coeFn_toLp

/-- The Fourier transform of an `L¹` distribution is its bounded classical
Fourier transform, regarded as an `L∞` distribution. -/
theorem fourier_L1 (f : Lp ℂ 1 (volume : Measure Space)) :
    𝓕 (f : 𝓢'(Space, ℂ)) = (frequencyL1 f : 𝓢'(Space, ℂ)) := by
  ext φ
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply (μ := (volume : Measure Space))]
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (f := (φ : Space → ℂ)) (g := (f : Space → ℂ))
    (μ := (volume : Measure Space)) (ν := (volume : Measure Space))
    (L := innerₗ Space) Real.continuous_fourierChar continuous_inner φ.integrable
    (L1.integrable_coeFn f)
  calc
    _ = ∫ x : Space, φ x • (𝓕 (f : Space → ℂ)) x := by
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

def pressureHat (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) :
    Lp ℂ ⊤ (volume : Measure Space) := rieszSymbolLp i j • frequencyL1 f

/-- `R_i R_j f`, defined for arbitrary integrable data. -/
def pressureL1 (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) : 𝓢'(Space, ℂ) :=
  𝓕⁻ (pressureHat i j f : 𝓢'(Space, ℂ))

theorem pressureHat_ae (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) :
    pressureHat i j f =ᵐ[volume]
      fun x => rieszSymbol i j x * (𝓕 (f : Space → ℂ)) x := by
  filter_upwards [Lp.coeFn_lpSMul (r := ⊤) (rieszSymbolLp i j) (frequencyL1 f),
    rieszSymbolLp_ae i j, frequencyL1_ae f] with x hm hs hf
  change pressureHat i j f x = _ at hm ⊢
  simpa only [Pi.smul_apply', smul_eq_mul, hs, hf] using hm

/-- The same Fourier symbol acts on `L²` by a contraction. -/
def pressureL2 (i j : Fin 3) (f : Lp ℂ 2 (volume : Measure Space)) :
    Lp ℂ 2 (volume : Measure Space) := 𝓕⁻ (rieszSymbolLp i j • 𝓕 f)

theorem norm_pressureL2_le (i j : Fin 3) (f : Lp ℂ 2 (volume : Measure Space)) :
    ‖pressureL2 i j f‖ ≤ ‖f‖ := by
  have hnorm (g : Lp ℂ 2 (volume : Measure Space)) : ‖𝓕⁻ g‖ = ‖g‖ :=
    (Lp.fourierTransformₗᵢ Space ℂ).symm.norm_map g
  rw [pressureL2, hnorm, ← Lp.norm_fourier_eq f]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (rieszSymbolLp i j) (𝓕 f),
    rieszSymbolLp_ae i j] with x hm hs
  rw [hm]
  change ‖rieszSymbolLp i j x • (𝓕 f) x‖ ≤ ‖(𝓕 f) x‖
  rw [hs, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_rieszSymbol_le i j x)

def sobolevWeight (x : Space) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-2 : ℝ))

theorem sobolevWeight_temperate : sobolevWeight.HasTemperateGrowth := by
  unfold sobolevWeight
  fun_prop

theorem sobolevWeight_memLp : MemLp sobolevWeight 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    sobolevWeight_temperate.1.continuous.aestronglyMeasurable).mpr
  have hi : Integrable (fun x : Space => (1 + ‖x‖ ^ 2) ^ (-4 : ℝ)) := by
    convert! (integrable_rpow_neg_one_add_norm_sq
      (μ := (volume : Measure Space)) (r := 8) (by norm_num)) using 1
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
theorem inverse_fourier_memSobolev (F : Lp ℂ ⊤ (volume : Measure Space)) :
    MemSobolev (-4) 2 (𝓕⁻ (F : 𝓢'(Space, ℂ))) := by
  apply memSobolev_iff_exists_smulLeftCLM_fourier.mpr
  use (sobolevWeight_memLp.toLp sobolevWeight • F : Lp ℂ 2 volume)
  rw [fourier_fourierInv_eq]
  have he := Lp.toTemperedDistribution_smul_eq (p := 2) (q := ⊤) (r := 2)
    sobolevWeight_temperate sobolevWeight_memLp F
  have hw : (fun x : Space => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((-4 : ℝ) / 2))) =
      sobolevWeight := by
    funext x
    simp only [sobolevWeight, show (-4 : ℝ) / 2 = -2 by norm_num]
  rw [hw]
  exact he.symm

theorem pressureL1_memSobolev (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) :
    MemSobolev (-4) 2 (pressureL1 i j f) :=
  inverse_fourier_memSobolev _

def coordinateSymbol (i : Fin 3) (x : Space) : ℂ := Complex.ofReal (x i)

def laplacianSymbol (x : Space) : ℂ := Complex.ofReal (‖x‖ ^ 2)

theorem coordinateSymbol_temperate (i : Fin 3) : (coordinateSymbol i).HasTemperateGrowth := by
  change (fun x : Space => Complex.ofRealCLM ((EuclideanSpace.proj i) x)).HasTemperateGrowth
  fun_prop

theorem laplacianSymbol_temperate : laplacianSymbol.HasTemperateGrowth := by
  unfold laplacianSymbol
  fun_prop

theorem rieszSymbol_poisson (i j : Fin 3) (x : Space) :
    laplacianSymbol x * rieszSymbol i j x = -(coordinateSymbol i x * coordinateSymbol j x) := by
  by_cases hx : x = 0
  · simp [laplacianSymbol, rieszSymbol, coordinateSymbol, hx]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  simp only [laplacianSymbol, rieszSymbol, coordinateSymbol, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg]
  congr 1
  field_simp

theorem pressureHat_poisson (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) :
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
  linear_combination φ x * (𝓕 (f : Space → ℂ)) x * hsym

theorem coordinateSymbol_eq_inner (i : Fin 3) :
    coordinateSymbol i = fun x : Space => Complex.ofReal (inner ℝ x (coordinateVector i)) := by
  funext x
  simp [coordinateSymbol, coordinateVector, EuclideanSpace.inner_single_right]

theorem fourier_second_derivative (i j : Fin 3) (f : 𝓢'(Space, ℂ)) :
    𝓕 (∂_{coordinateVector i} (∂_{coordinateVector j} f)) =
      -(2 * Real.pi : ℂ) ^ 2 •
        smulLeftCLM ℂ (coordinateSymbol i * coordinateSymbol j) (𝓕 f) := by
  rw [fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
  rw [← coordinateSymbol_eq_inner i, ← coordinateSymbol_eq_inner j]
  rw [map_smul, smul_smul,
    smulLeftCLM_smulLeftCLM_apply (coordinateSymbol_temperate j) (coordinateSymbol_temperate i),
    mul_comm (coordinateSymbol j) (coordinateSymbol i)]
  congr 1
  ring_nf
  simp

theorem fourier_laplacian (f : 𝓢'(Space, ℂ)) :
    𝓕 (Δ f) = -(2 * Real.pi : ℂ) ^ 2 • smulLeftCLM ℂ laplacianSymbol (𝓕 f) := by
  rw [laplacian_eq_fourierMultiplierCLM, ← Complex.coe_smul, FourierTransform.fourier_smul,
    fourierMultiplierCLM_apply, fourier_fourierInv_eq]
  simp only [Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hl : (fun x : Space => (‖x‖ : ℂ) ^ 2) = laplacianSymbol := by
    funext x
    simp [laplacianSymbol]
  rw [hl]

/-- The normalized pressure of an integrable stress component solves the
Poisson equation with its two distributional derivatives. -/
theorem pressureL1_poisson (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) :
    Δ (pressureL1 i j f) = -∂_{coordinateVector i} (∂_{coordinateVector j}
      (f : 𝓢'(Space, ℂ))) := by
  have he : 𝓕 (Δ (pressureL1 i j f)) =
      𝓕 (-∂_{coordinateVector i} (∂_{coordinateVector j} (f : 𝓢'(Space, ℂ)))) := by
    rw [fourier_laplacian, pressureL1, fourier_fourierInv_eq, pressureHat_poisson,
      FourierTransform.fourier_neg, fourier_second_derivative, fourier_L1]
    module
  have hi := congrArg (fun g : 𝓢'(Space, ℂ) => 𝓕⁻ g) he
  simpa only [fourierInv_fourier_eq] using hi

theorem lp_distribution_eq_of_ae {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {f : Lp ℂ p (volume : Measure Space)} {g : Lp ℂ q (volume : Measure Space)}
    (h : (f : Space → ℂ) =ᵐ[volume] g) : (f : 𝓢'(Space, ℂ)) = (g : 𝓢'(Space, ℂ)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- The `Lp` embeddings are compatible even when their exponents differ. -/
theorem lp_ae_of_distribution_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {f : Lp ℂ p (volume : Measure Space)} {g : Lp ℂ q (volume : Measure Space)}
    (h : (f : 𝓢'(Space, ℂ)) = (g : 𝓢'(Space, ℂ))) :
    (f : Space → ℂ) =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable Fact.out) ((Lp.memLp g).locallyIntegrable Fact.out)
  intro φ hφ hc
  have hcomp : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hc.comp_left rfl
  have hsmooth : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  have he := congrArg (fun F : 𝓢'(Space, ℂ) => F (hcomp.toSchwartzMap hsmooth)) h
  simpa using he

/-- On data which belong to both spaces, the `L¹` pressure distribution is
exactly the `L²` Riesz transform. -/
theorem pressureL1_eq_pressureL2 (i j : Fin 3)
    {f : Lp ℂ 1 (volume : Measure Space)} {g : Lp ℂ 2 (volume : Measure Space)}
    (h : (f : Space → ℂ) =ᵐ[volume] g) :
    pressureL1 i j f = (pressureL2 i j g : 𝓢'(Space, ℂ)) := by
  have hfreq : (frequencyL1 f : 𝓢'(Space, ℂ)) = (𝓕 g : Lp ℂ 2 volume) := by
    rw [← fourier_L1, ← Lp.fourier_toTemperedDistribution_eq, lp_distribution_eq_of_ae h]
  have hfreqae := lp_ae_of_distribution_eq hfreq
  have hprod : (pressureHat i j f : 𝓢'(Space, ℂ)) =
      (rieszSymbolLp i j • 𝓕 g : Lp ℂ 2 volume) := by
    apply lp_distribution_eq_of_ae
    filter_upwards [Lp.coeFn_lpSMul (r := ⊤) (rieszSymbolLp i j) (frequencyL1 f),
      Lp.coeFn_lpSMul (r := 2) (rieszSymbolLp i j) (𝓕 g), hfreqae] with x hleft hright heq
    change pressureHat i j f x = _ at hleft ⊢
    rw [hleft, hright]
    simp only [Pi.smul_apply', heq]
  rw [pressureL1, hprod, Lp.fourierInv_toTemperedDistribution_eq]
  rfl

theorem norm_Lp_top_le_of_ae_bound {F : Lp ℂ ⊤ (volume : Measure Space)} {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ᵐ x ∂volume, ‖F x‖ ≤ C) : ‖F‖ ≤ C := by
  have hb := eLpNormEssSup_le_of_ae_bound hF
  have hr := ENNReal.toReal_mono (by finiteness) hb
  simpa only [Lp.norm_def, eLpNorm_exponent_top, ENNReal.toReal_ofReal hC] using hr

theorem norm_classical_fourier_le (f : Lp ℂ 1 (volume : Measure Space)) (x : Space) :
    ‖𝓕 (f : Space → ℂ) x‖ ≤ ‖f‖ := by
  rw [Real.fourier_eq]
  apply (norm_integral_le_integral_norm _).trans
  simp only [Circle.norm_smul]
  exact (L1.norm_eq_integral_norm f).symm.le

theorem norm_pressureHat_le (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) :
    ‖pressureHat i j f‖ ≤ ‖f‖ := by
  apply norm_Lp_top_le_of_ae_bound (norm_nonneg _)
  filter_upwards [pressureHat_ae i j f] with x hx
  rw [hx, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_rieszSymbol_le i j x)).trans
    (norm_classical_fourier_le f x)

theorem frequencyL1_add (f g : Lp ℂ 1 (volume : Measure Space)) :
    frequencyL1 (f + g) = frequencyL1 f + frequencyL1 g := by
  apply Lp.ext
  filter_upwards [frequencyL1_ae (f + g), frequencyL1_ae f, frequencyL1_ae g,
    Lp.coeFn_add (frequencyL1 f) (frequencyL1 g)] with x hs hf hg ha
  rw [ha, hs, Pi.add_apply, hf, hg]
  exact congrArg (fun F : BoundedContinuousFunction Space ℂ => F x)
    (map_add (Real.Lp.fourierTransformCLM Space ℂ) f g)

theorem frequencyL1_smul (c : ℂ) (f : Lp ℂ 1 (volume : Measure Space)) :
    frequencyL1 (c • f) = c • frequencyL1 f := by
  apply Lp.ext
  filter_upwards [frequencyL1_ae (c • f), frequencyL1_ae f,
    Lp.coeFn_smul c (frequencyL1 f)] with x hs hf ha
  rw [ha, hs, Pi.smul_apply, hf]
  exact congrArg (fun F : BoundedContinuousFunction Space ℂ => F x)
    (map_smul (Real.Lp.fourierTransformCLM Space ℂ) c f)

def pressureHatCLM (i j : Fin 3) :
    Lp ℂ 1 (volume : Measure Space) →L[ℂ] Lp ℂ ⊤ (volume : Measure Space) :=
  LinearMap.mkContinuous
    { toFun := pressureHat i j
      map_add' := by
        intro f g
        simp only [pressureHat, frequencyL1_add, Lp.add_smul]
      map_smul' := by
        intro c f
        simp only [pressureHat, frequencyL1_smul, RingHom.id_apply]
        exact (Lp.smul_comm c (rieszSymbolLp i j) (frequencyL1 f)).symm }
    1 (fun f => by
      change ‖pressureHat i j f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_pressureHat_le i j f)

/-- Continuity in the `L¹` stress, with values in tempered distributions,
justifies the approximation step in the pressure representation. -/
def pressureL1CLM (i j : Fin 3) : Lp ℂ 1 (volume : Measure Space) →L[ℂ] 𝓢'(Space, ℂ) :=
  fourierInvCLM ℂ 𝓢'(Space, ℂ) ∘L Lp.toTemperedDistributionCLM ℂ volume ⊤ ∘L
    pressureHatCLM i j

@[simp] theorem pressureL1CLM_apply (i j : Fin 3) (f : Lp ℂ 1 (volume : Measure Space)) :
    pressureL1CLM i j f = pressureL1 i j f := rfl

theorem pressureL1_continuous (i j : Fin 3) : Continuous (pressureL1 i j) :=
  (pressureL1CLM i j).continuous

def stressPressure (g : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Space)) : 𝓢'(Space, ℂ) :=
  ∑ i, ∑ j, pressureL1 i j (g i j)

theorem laplacian_finset_sum {ι : Type*} (s : Finset ι) (F : ι → 𝓢'(Space, ℂ)) :
    Δ (∑ i ∈ s, F i) = ∑ i ∈ s, Δ (F i) := by
  simpa only [laplacianCLM_apply] using
    (map_sum (LineDeriv.laplacianCLM ℂ Space 𝓢'(Space, ℂ)) F s)

theorem memSobolev_finset_sum {ι : Type*} (s : Finset ι) {r : ℝ} (F : ι → 𝓢'(Space, ℂ))
    (hF : ∀ i ∈ s, MemSobolev r 2 (F i)) : MemSobolev r 2 (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero Space ℂ r 2
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- The pressure source for a complete integrable stress tensor. -/
theorem stressPressure_poisson (g : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Space)) :
    Δ (stressPressure g) =
      -(∑ i, ∑ j, ∂_{coordinateVector i} (∂_{coordinateVector j}
        (g i j : 𝓢'(Space, ℂ)))) := by
  simp only [stressPressure, laplacian_finset_sum, pressureL1_poisson, Finset.sum_neg_distrib]

theorem stressPressure_memSobolev (g : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Space)) :
    MemSobolev (-4) 2 (stressPressure g) := by
  apply memSobolev_finset_sum
  intro i _
  exact memSobolev_finset_sum _ _ (fun j _ => pressureL1_memSobolev i j (g i j))

theorem laplacian_lineDeriv (f : 𝓢'(Space, ℂ)) (m : Space) :
    Δ (∂_{m} f) = ∂_{m} (Δ f) := by
  have hm : (fun x : Space => Complex.ofReal (inner ℝ x m)).HasTemperateGrowth := by fun_prop
  have he : 𝓕 (Δ (∂_{m} f)) = 𝓕 (∂_{m} (Δ f)) := by
    simp only [fourier_laplacian, fourier_lineDerivOp_eq, map_smul, smul_smul]
    rw [smulLeftCLM_smulLeftCLM_apply hm laplacianSymbol_temperate,
      smulLeftCLM_smulLeftCLM_apply laplacianSymbol_temperate hm,
      mul_comm laplacianSymbol (fun x : Space => Complex.ofReal (inner ℝ x m))]
    module
  have hi := congrArg (fun g : 𝓢'(Space, ℂ) => 𝓕⁻ g) he
  simpa only [fourierInv_fourier_eq] using hi

theorem eq_of_laplacian_eq {r : ℝ} {f g : 𝓢'(Space, ℂ)}
    (hf : MemSobolev r 2 f) (hg : MemSobolev r 2 g) (he : Δ f = Δ g) : f = g := by
  apply sub_eq_zero.mp
  apply R3HarmonicPressure.eq_zero_of_harmonic_memSobolev (hf.sub hg)
  rw [← laplacianCLM_apply, map_sub, laplacianCLM_apply, laplacianCLM_apply, he, sub_self]

/-- In the negative Sobolev class supplied by the finite-energy equation,
the pressure gradient is uniquely determined by the integrable stress. -/
theorem stressPressure_gradient_unique
    (g : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Space)) (m : Space)
    {P : 𝓢'(Space, ℂ)} (hP : MemSobolev (-5) 2 P)
    (hsource : Δ P = -∂_{m}
      (∑ i, ∑ j, ∂_{coordinateVector i} (∂_{coordinateVector j}
        (g i j : 𝓢'(Space, ℂ))))) :
    P = ∂_{m} (stressPressure g) := by
  apply eq_of_laplacian_eq hP
  · convert! (stressPressure_memSobolev g).lineDerivOp (m := m) using 1
    norm_num
  · rw [laplacian_lineDeriv, stressPressure_poisson, LineDeriv.lineDerivOp_neg]
    exact hsource

end NavierStokes.R3PressureFourier
