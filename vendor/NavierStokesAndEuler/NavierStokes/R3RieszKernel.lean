import NavierStokes.R3GaussianPressure
import NavierStokes.R3PressureCommutator

/-!
# Integral kernels for the regularized second-order Riesz transforms

Integrating normalized Gaussian Hessians over positive scales produces the
Riesz multiplier. Finite scale intervals give integrable kernels, uniformly
bounded by a constant times `|x|⁻³` away from the origin.
-/

noncomputable section
namespace NavierStokes.R3RieszKernel

open Set Filter MeasureTheory ProblemStatement FourierTransform R3GaussianPressure
open scoped Topology

def density (a : ℝ) (i j : Fin 3) (x : Space) : ℂ :=
  ((Real.pi ^ (-3 / 2 : ℝ) / 4 * a ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * secondGaussian a i j x

def densityMajorant (a r : ℝ) : ℝ :=
  Real.pi ^ (-3 / 2 : ℝ) *
    (r ^ 2 * a ^ (3 / 2 : ℝ) + (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ)) * Real.exp (-a * r ^ 2)

def kernelConstant : ℝ :=
  Real.pi ^ (-3 / 2 : ℝ) * (Real.Gamma (5 / 2) + (1 / 2 : ℝ) * Real.Gamma (3 / 2))

theorem kernelConstant_nonneg : 0 ≤ kernelConstant := by unfold kernelConstant; positivity

theorem density_measurable (i j : Fin 3) : Measurable (fun p : ℝ × Space => density p.1 i j p.2) := by
  unfold density secondGaussian gaussianReal
  fun_prop

theorem density_integrable {a : ℝ} (ha : 0 < a) (i j : Fin 3) : Integrable (density a i j) :=
  (secondGaussian_integrable ha i j).const_mul _

theorem density_formula {a : ℝ} (ha : 0 < a) (i j : Fin 3) (x : Space) :
    density a i j x = ((Real.pi ^ (-3 / 2 : ℝ) *
      (a ^ (3 / 2 : ℝ) * x i * x j - (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) *
        (if i = j then 1 else 0)) * gaussianReal a x : ℝ) : ℂ) := by
  have h₁ : a ^ (-1 / 2 : ℝ) * a ^ 2 = a ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_add ha]
    norm_num
  have h₂ : a ^ (-1 / 2 : ℝ) * a = a ^ (1 / 2 : ℝ) := by
    nth_rw 2 [← Real.rpow_one a]
    rw [← Real.rpow_add ha]
    norm_num
  unfold density secondGaussian
  rw [← Complex.ofReal_mul]
  congr 1
  have he : Real.pi ^ (-3 / 2 : ℝ) / 4 * a ^ (-1 / 2 : ℝ) *
      ((4 * a ^ 2 * x i * x j - 2 * a * (if i = j then 1 else 0)) * gaussianReal a x) =
      Real.pi ^ (-3 / 2 : ℝ) *
        ((a ^ (-1 / 2 : ℝ) * a ^ 2) * x i * x j -
          (1 / 2 : ℝ) * (a ^ (-1 / 2 : ℝ) * a) * (if i = j then 1 else 0)) * gaussianReal a x := by ring
  rw [he, h₁, h₂]

theorem norm_density_le {a : ℝ} (ha : 0 < a) (i j : Fin 3) (x : Space) :
    ‖density a i j x‖ ≤ densityMajorant a ‖x‖ := by
  rw [density_formula ha, Complex.norm_real, Real.norm_eq_abs]
  have hp : 0 ≤ Real.pi ^ (-3 / 2 : ℝ) := by positivity
  have ha₃ : 0 ≤ a ^ (3 / 2 : ℝ) := Real.rpow_nonneg ha.le _
  have ha₁ : 0 ≤ a ^ (1 / 2 : ℝ) := Real.rpow_nonneg ha.le _
  have hij : |(if i = j then 1 else 0 : ℝ)| ≤ 1 := by split <;> norm_num
  have hprod : |x i| * |x j| ≤ ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, pow_two] using
      mul_le_mul (PiLp.norm_apply_le x i) (PiLp.norm_apply_le x j)
        (norm_nonneg (x j)) (norm_nonneg x)
  rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_pos (gaussianReal_pos a x)]
  apply mul_le_mul_of_nonneg_right _ (gaussianReal_pos a x).le
  apply mul_le_mul_of_nonneg_left _ hp
  calc
    _ ≤ |a ^ (3 / 2 : ℝ) * x i * x j| +
        |(1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) * (if i = j then 1 else 0)| := abs_sub _ _
    _ = a ^ (3 / 2 : ℝ) * (|x i| * |x j|) +
        (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) * |(if i = j then 1 else 0)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha₃, abs_of_nonneg ha₁]
      norm_num
      ring
    _ ≤ _ := by nlinarith

theorem densityMajorant_nonneg {a : ℝ} (ha : 0 ≤ a) (r : ℝ) : 0 ≤ densityMajorant a r := by
  unfold densityMajorant
  positivity

theorem gamma_moment_integrable {r q : ℝ} (hr : 0 < r) (hq : -1 < q) :
    IntegrableOn (fun a : ℝ => a ^ q * Real.exp (-a * r ^ 2)) (Ioi 0) := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (s := q) (p := 1)
    hq (by norm_num) (sq_pos_of_pos hr)
  simpa only [Real.rpow_one, mul_comm (r ^ 2), neg_mul] using hh

theorem densityMajorant_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun a => densityMajorant a r) (Ioi 0) := by
  have h₃ := (gamma_moment_integrable (q := 3 / 2) hr (by norm_num)).const_mul (r ^ 2)
  have h₁ := (gamma_moment_integrable (q := 1 / 2) hr (by norm_num)).const_mul (1 / 2 : ℝ)
  apply ((h₃.add h₁).const_mul (Real.pi ^ (-3 / 2 : ℝ))).congr
  filter_upwards with a
  unfold densityMajorant
  simp only [Pi.add_apply]
  ring

theorem inverse_radius_power {r q : ℝ} (hr : 0 < r) :
    (1 / r ^ 2) ^ q = r ^ (-2 * q) := by
  rw [one_div, Real.inv_rpow (sq_nonneg r), ← Real.rpow_neg (sq_nonneg r),
    ← Real.rpow_natCast_mul hr.le]
  congr 1
  ring

theorem integral_densityMajorant {r : ℝ} (hr : 0 < r) :
    (∫ a : ℝ in Ioi 0, densityMajorant a r) = kernelConstant * r ^ (-3 : ℝ) := by
  have h₃ := gamma_moment_integrable (q := 3 / 2) hr (by norm_num)
  have h₁ := gamma_moment_integrable (q := 1 / 2) hr (by norm_num)
  have he (a : ℝ) : densityMajorant a r = Real.pi ^ (-3 / 2 : ℝ) *
      (r ^ 2 * (a ^ (3 / 2 : ℝ) * Real.exp (-(r ^ 2 * a))) +
        (1 / 2 : ℝ) * (a ^ (1 / 2 : ℝ) * Real.exp (-(r ^ 2 * a)))) := by
    unfold densityMajorant
    simp only [neg_mul]
    rw [mul_comm (r ^ 2) a]
    ring
  have h₃' : IntegrableOn (fun a : ℝ => a ^ (3 / 2 : ℝ) * Real.exp (-(r ^ 2 * a))) (Ioi 0) := by
    simpa only [neg_mul, mul_comm (r ^ 2)] using h₃
  have h₁' : IntegrableOn (fun a : ℝ => a ^ (1 / 2 : ℝ) * Real.exp (-(r ^ 2 * a))) (Ioi 0) := by
    simpa only [neg_mul, mul_comm (r ^ 2)] using h₁
  simp_rw [he]
  rw [integral_const_mul, integral_add (h₃'.const_mul (r ^ 2)) (h₁'.const_mul (1 / 2 : ℝ)),
    integral_const_mul, integral_const_mul]
  have hΓ₃ := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 5 / 2) (by norm_num) (sq_pos_of_pos hr)
  have hΓ₁ := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3 / 2) (by norm_num) (sq_pos_of_pos hr)
  norm_num only [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num,
    show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at hΓ₃ hΓ₁
  rw [hΓ₃, hΓ₁, inverse_radius_power hr, inverse_radius_power hr]
  norm_num [kernelConstant]
  field_simp

theorem density_integrable_scale {x : Space} (hx : x ≠ 0) (i j : Fin 3) :
    IntegrableOn (fun a => density a i j x) (Ioi 0) := by
  apply (densityMajorant_integrable (norm_pos_iff.mpr hx)).mono'
    ((density_measurable i j).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact norm_density_le ha i j x


/-- Exact multiplier of the Gaussian density. -/
theorem fourier_density {a : ℝ} (ha : 0 < a) (i j : Fin 3) (ξ : Space) :
    𝓕 (density a i j) ξ =
      ((-Real.pi ^ 2 * ξ i * ξ j / a ^ 2 * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / a) : ℝ) : ℂ) := by
  have hlin : 𝓕 (density a i j) ξ =
      ((Real.pi ^ (-3 / 2 : ℝ) / 4 * a ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        𝓕 (secondGaussian a i j) ξ := by
    simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, density]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hlin, fourier_secondGaussian ha, fourier_gaussian ha]
  have hpow : Real.pi ^ (-3 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) *
      (Real.pi / a) ^ (3 / 2 : ℝ) = a ^ (-2 : ℝ) := by
    rw [Real.div_rpow Real.pi_pos.le ha.le]
    rw [div_eq_mul_inv (Real.pi ^ (3 / 2 : ℝ)) (a ^ (3 / 2 : ℝ)), ← Real.rpow_neg ha.le]
    calc
      _ = (Real.pi ^ (-3 / 2 : ℝ) * Real.pi ^ (3 / 2 : ℝ)) *
          (a ^ (-1 / 2 : ℝ) * a ^ (-(3 / 2) : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add Real.pi_pos, ← Real.rpow_add ha]; norm_num
  push_cast
  have hc := congrArg Complex.ofReal hpow
  push_cast at hc
  calc
    _ = -(Real.pi : ℂ) ^ 2 * (ξ i : ℂ) * (ξ j : ℂ) *
        ((Real.pi ^ (-3 / 2 : ℝ) : ℝ) * (a ^ (-1 / 2 : ℝ) : ℝ) *
          ((Real.pi / a) ^ (3 / 2 : ℝ) : ℝ)) *
        (Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / a) : ℂ) := by push_cast; ring
    _ = _ := by rw [hc]; norm_num; ring

def intervalKernel (lo hi : ℝ) (i j : Fin 3) (x : Space) : ℂ :=
  ∫ a : ℝ in Icc lo hi, density a i j x

def limitingKernel (i j : Fin 3) (x : Space) : ℂ :=
  ∫ a : ℝ in Ioi 0, density a i j x

theorem intervalKernel_measurable (lo hi : ℝ) (i j : Fin 3) :
    Measurable (intervalKernel lo hi i j) :=
  (density_measurable i j).stronglyMeasurable.integral_prod_left'.measurable

theorem limitingKernel_measurable (i j : Fin 3) : Measurable (limitingKernel i j) :=
  (density_measurable i j).stronglyMeasurable.integral_prod_left'.measurable

theorem intervalKernel_bound {lo hi : ℝ} (hlo : 0 < lo) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ‖intervalKernel lo hi i j x‖ ≤ kernelConstant * ‖x‖ ^ (-3 : ℝ) := by
  have hsub : Icc lo hi ⊆ Ioi (0 : ℝ) := fun _ h => lt_of_lt_of_le hlo h.1
  have hb := densityMajorant_integrable (norm_pos_iff.mpr hx)
  have hh := norm_integral_le_of_norm_le (hb.mono_set hsub) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    exact norm_density_le (hsub ha) i j x)
  refine hh.trans ?_
  rw [← integral_densityMajorant (norm_pos_iff.mpr hx)]
  exact setIntegral_mono_set hb (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact densityMajorant_nonneg ha.le ‖x‖) (Eventually.of_forall hsub)

theorem limitingKernel_bound (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ‖limitingKernel i j x‖ ≤ kernelConstant * ‖x‖ ^ (-3 : ℝ) := by
  rw [← integral_densityMajorant (norm_pos_iff.mpr hx)]
  apply norm_integral_le_of_norm_le (densityMajorant_integrable (norm_pos_iff.mpr hx))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact norm_density_le ha i j x

theorem intervalKernel_kernelBound {lo hi : ℝ} (hlo : 0 < lo) (i j : Fin 3) :
    R3PressureCommutator.KernelBound kernelConstant (intervalKernel lo hi i j) :=
  ⟨kernelConstant_nonneg, intervalKernel_measurable lo hi i j, intervalKernel_bound hlo i j⟩

theorem limitingKernel_kernelBound (i j : Fin 3) :
    R3PressureCommutator.KernelBound kernelConstant (limitingKernel i j) :=
  ⟨kernelConstant_nonneg, limitingKernel_measurable i j, limitingKernel_bound i j⟩

def scaleInterval (n : ℕ) : Set ℝ := Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1)

theorem scaleInterval_pos (n : ℕ) : scaleInterval n ⊆ Ioi (0 : ℝ) :=
  fun _ h => lt_of_lt_of_le (by positivity) h.1

theorem scaleInterval_mono : Monotone scaleInterval := by
  intro n m hnm a ha
  have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
  refine ⟨?_, ha.2.trans (by linarith)⟩
  exact (inv_anti₀ (by positivity : 0 < (n : ℝ) + 1) (by linarith)).trans ha.1

theorem scaleInterval_union : (⋃ n, scaleInterval n) = Ioi (0 : ℝ) := by
  ext a
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact scaleInterval_pos n hn
  · intro ha
    obtain ⟨n, hn⟩ := exists_nat_gt (max a a⁻¹)
    apply mem_iUnion.mpr
    use n
    have hna : a < (n : ℝ) := (le_max_left _ _).trans_lt hn
    have hni : a⁻¹ < (n : ℝ) := (le_max_right _ _).trans_lt hn
    refine ⟨?_, by linarith⟩
    have hh := inv_anti₀ (inv_pos.mpr ha) (show a⁻¹ ≤ (n : ℝ) + 1 by linarith)
    simpa only [inv_inv] using hh

def truncatedKernel (n : ℕ) (i j : Fin 3) : Space → ℂ :=
  intervalKernel ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) i j

theorem truncatedKernel_kernelBound (n : ℕ) (i j : Fin 3) :
    R3PressureCommutator.KernelBound kernelConstant (truncatedKernel n i j) :=
  intervalKernel_kernelBound (by positivity) i j

theorem truncatedKernel_tendsto (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    Tendsto (fun n => truncatedKernel n i j x) atTop (𝓝 (limitingKernel i j x)) := by
  have hi : IntegrableOn (fun a => density a i j x) (⋃ n, scaleInterval n) := by
    rw [scaleInterval_union]
    exact density_integrable_scale hx i j
  have ht := tendsto_setIntegral_of_monotone (s := scaleInterval) (fun _ => measurableSet_Icc) scaleInterval_mono hi
  rw [scaleInterval_union] at ht
  exact ht


def spatialEnvelope (lo hi : ℝ) (x : Space) : ℝ :=
  Real.pi ^ (-3 / 2 : ℝ) *
    (‖x‖ ^ 2 * hi ^ (3 / 2 : ℝ) + (1 / 2 : ℝ) * hi ^ (1 / 2 : ℝ)) * gaussianReal lo x

theorem spatialEnvelope_integrable {lo hi : ℝ} (hlo : 0 < lo) :
    Integrable (spatialEnvelope lo hi) := by
  have h₂ := (gaussian_moment_integrable hlo 2).const_mul (hi ^ (3 / 2 : ℝ))
  have h₀ := (gaussianReal_integrable hlo).const_mul ((1 / 2 : ℝ) * hi ^ (1 / 2 : ℝ))
  apply ((h₂.add h₀).const_mul (Real.pi ^ (-3 / 2 : ℝ))).congr
  filter_upwards with x
  unfold spatialEnvelope
  simp only [Pi.add_apply]
  ring

theorem densityMajorant_le_envelope {lo hi a : ℝ} (hlo : 0 < lo) (ha : a ∈ Icc lo hi) (x : Space) :
    densityMajorant a ‖x‖ ≤ spatialEnvelope lo hi x := by
  have hapos : 0 < a := hlo.trans_le ha.1
  have hhipos : 0 < hi := hapos.trans_le ha.2
  have h₃ := Real.rpow_le_rpow hapos.le ha.2 (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have h₁ := Real.rpow_le_rpow hapos.le ha.2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he : Real.exp (-a * ‖x‖ ^ 2) ≤ Real.exp (-lo * ‖x‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg ha.1) (sq_nonneg _)
  unfold densityMajorant spatialEnvelope gaussianReal
  have hc : 0 ≤ Real.pi ^ (-3 / 2 : ℝ) := by positivity
  apply mul_le_mul _ he (by positivity) (by positivity)
  apply mul_le_mul_of_nonneg_left _ hc
  nlinarith [sq_nonneg ‖x‖]

theorem density_integrable_product {lo hi : ℝ} (hlo : 0 < lo) (i j : Fin 3) :
    Integrable (fun p : ℝ × Space => density p.1 i j p.2)
      ((volume.restrict (Icc lo hi)).prod volume) := by
  have he : Integrable (fun p : ℝ × Space => spatialEnvelope lo hi p.2)
      ((volume.restrict (Icc lo hi)).prod volume) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Icc lo hi))).mul_prod (spatialEnvelope_integrable (hi := hi) hlo)
  apply he.mono' (density_measurable i j).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with p hp
  exact (norm_density_le (hlo.trans_le hp.1) i j p.2).trans (densityMajorant_le_envelope hlo hp p.2)

theorem intervalKernel_integrable {lo hi : ℝ} (hlo : 0 < lo) (i j : Fin 3) :
    Integrable (intervalKernel lo hi i j) :=
  (density_integrable_product hlo i j).integral_prod_right

/-- Fubini is applicable before computing the truncated multiplier. -/
theorem fourier_intervalKernel_integral {lo hi : ℝ} (hlo : 0 < lo) (i j : Fin 3) (ξ : Space) :
    𝓕 (intervalKernel lo hi i j) ξ = ∫ a : ℝ in Icc lo hi, 𝓕 (density a i j) ξ := by
  let c (x : Space) : ℂ := Real.fourierChar (-inner ℝ x ξ)
  have hm : Measurable c := by unfold c; fun_prop
  have hc (x : Space) : ‖c x‖ = 1 := Circle.norm_coe _
  have ht : Integrable (fun p : ℝ × Space => c p.2 * density p.1 i j p.2)
      ((volume.restrict (Icc lo hi)).prod volume) := by
    apply (density_integrable_product hlo i j).mono
      ((hm.comp measurable_snd).mul (density_measurable i j)).aestronglyMeasurable
    filter_upwards with p
    change ‖c p.2 * density p.1 i j p.2‖ ≤ ‖density p.1 i j p.2‖
    simp only [norm_mul, hc, one_mul, le_refl]
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, intervalKernel]
  simp_rw [← integral_const_mul]
  exact integral_integral_swap ht.swap


def scaleFactor (lo hi : ℝ) (ξ : Space) : ℝ :=
  Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / hi) - Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / lo)

theorem multiplier_primitive {a : ℝ} (ha : 0 < a) (i j : Fin 3) (ξ : Space) :
    HasDerivAt (fun b : ℝ => (-(ξ i * ξ j) / ‖ξ‖ ^ 2) *
        Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / b))
      (-Real.pi ^ 2 * ξ i * ξ j / a ^ 2 * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / a)) a := by
  by_cases hξ : ξ = 0
  · subst ξ
    simpa using (hasDerivAt_const a (0 : ℝ))
  have hd := (((hasDerivAt_id a).inv ha.ne').const_mul (-Real.pi ^ 2 * ‖ξ‖ ^ 2)).exp
  have hm := hd.const_mul (-(ξ i * ξ j) / ‖ξ‖ ^ 2)
  convert! hm using 1
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  simp only [Pi.inv_apply, id_eq]
  field_simp

theorem fourier_intervalKernel {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (i j : Fin 3) (ξ : Space) :
    𝓕 (intervalKernel lo hi i j) ξ =
      R3PressureFourier.rieszSymbol i j ξ * (scaleFactor lo hi ξ : ℂ) := by
  rw [fourier_intervalKernel_integral hlo]
  have he : (∫ a : ℝ in Icc lo hi, 𝓕 (density a i j) ξ) =
      ((∫ a : ℝ in Icc lo hi, -Real.pi ^ 2 * ξ i * ξ j / a ^ 2 *
        Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / a) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Icc
    intro a ha
    exact fourier_density (hlo.trans_le ha.1) i j ξ
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hd : ∀ a ∈ uIcc lo hi, HasDerivAt
      (fun b : ℝ => (-(ξ i * ξ j) / ‖ξ‖ ^ 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / b))
      (-Real.pi ^ 2 * ξ i * ξ j / a ^ 2 * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / a)) a := by
    intro a ha
    rw [uIcc_of_le hle] at ha
    exact multiplier_primitive (hlo.trans_le ha.1) i j ξ
  have hc : ContinuousOn (fun a : ℝ => -Real.pi ^ 2 * ξ i * ξ j / a ^ 2 *
      Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / a)) (Icc lo hi) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.div (continuousOn_id.pow 2) (fun a ha => pow_ne_zero _ (hlo.trans_le ha.1).ne')
    · exact (continuousOn_const.div continuousOn_id (fun a ha => (hlo.trans_le ha.1).ne')).rexp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hle)]
  unfold R3PressureFourier.rieszSymbol scaleFactor
  push_cast
  ring

theorem scaleFactor_mem_Icc {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi) (ξ : Space) :
    scaleFactor lo hi ξ ∈ Icc (0 : ℝ) 1 := by
  have hhi : 0 < hi := hlo.trans_le hle
  have hB : 0 ≤ Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have he : -Real.pi ^ 2 * ‖ξ‖ ^ 2 / lo ≤ -Real.pi ^ 2 * ‖ξ‖ ^ 2 / hi := by
    have hd := div_le_div_of_nonneg_left hB hlo hle
    simpa only [neg_mul, neg_div] using neg_le_neg hd
  have hnonpos : -Real.pi ^ 2 * ‖ξ‖ ^ 2 / hi ≤ 0 := by
    simpa only [neg_mul, neg_div] using neg_nonpos.mpr (div_nonneg hB hhi.le)
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_exp.mpr he)
  · unfold scaleFactor
    nlinarith [Real.exp_pos (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / lo),
      Real.exp_le_one_iff.mpr hnonpos]

theorem norm_fourier_intervalKernel_le {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (i j : Fin 3) (ξ : Space) : ‖𝓕 (intervalKernel lo hi i j) ξ‖ ≤ 1 := by
  rw [fourier_intervalKernel hlo hle, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (scaleFactor_mem_Icc hlo hle ξ).1]
  exact (mul_le_of_le_one_left (scaleFactor_mem_Icc hlo hle ξ).1
    (R3PressureFourier.norm_rieszSymbol_le i j ξ)).trans (scaleFactor_mem_Icc hlo hle ξ).2


theorem scaleInterval_endpoints (n : ℕ) : ((n : ℝ) + 1)⁻¹ ≤ (n : ℝ) + 1 := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1) hn
  have hh' : ((n : ℝ) + 1)⁻¹ ≤ 1 := by simpa only [inv_one] using hh
  exact hh'.trans hn

theorem truncatedKernel_integrable (n : ℕ) (i j : Fin 3) : Integrable (truncatedKernel n i j) :=
  intervalKernel_integrable (by positivity) i j

theorem norm_fourier_truncatedKernel_le (n : ℕ) (i j : Fin 3) (ξ : Space) :
    ‖𝓕 (truncatedKernel n i j) ξ‖ ≤ 1 :=
  norm_fourier_intervalKernel_le (by positivity) (scaleInterval_endpoints n) i j ξ

theorem scaleFactor_truncated_tendsto (ξ : Space) (hξ : ξ ≠ 0) :
    Tendsto (fun n : ℕ => scaleFactor ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) ξ) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ)))
  have hB : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 := mul_pos (sq_pos_of_pos Real.pi_pos)
    (sq_pos_of_pos (norm_pos_iff.mpr hξ))
  have h₁ : Tendsto (fun n : ℕ => Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / ((n : ℝ) + 1)))
      atTop (𝓝 1) := by
    have hdiv : Tendsto (fun n : ℕ => -Real.pi ^ 2 * ‖ξ‖ ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero, div_eq_mul_inv] using
        (tendsto_inv_atTop_zero.comp hn).const_mul (-Real.pi ^ 2 * ‖ξ‖ ^ 2)
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp hdiv
  have h₀ : Tendsto (fun n : ℕ => Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / ((n : ℝ) + 1)⁻¹))
      atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hn.const_mul_atTop hB)
    simpa only [div_inv_eq_mul, neg_mul, Function.comp_def] using hh
  simpa only [scaleFactor, sub_zero] using h₁.sub h₀

/-- The regularized Fourier multipliers converge to the actual Riesz
symbol, including its assigned value at the origin. -/
theorem fourier_truncatedKernel_tendsto (i j : Fin 3) (ξ : Space) :
    Tendsto (fun n => 𝓕 (truncatedKernel n i j) ξ) atTop
      (𝓝 (R3PressureFourier.rieszSymbol i j ξ)) := by
  have he (n : ℕ) : 𝓕 (truncatedKernel n i j) ξ =
      R3PressureFourier.rieszSymbol i j ξ *
        (scaleFactor ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) ξ : ℂ) :=
    fourier_intervalKernel (by positivity) (scaleInterval_endpoints n) i j ξ
  by_cases hξ : ξ = 0
  · subst ξ
    simpa only [he, R3PressureFourier.rieszSymbol, PiLp.zero_apply, norm_zero, mul_zero,
      neg_zero, zero_div, Complex.ofReal_zero, zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have hh := (Complex.continuous_ofReal.tendsto 1).comp (scaleFactor_truncated_tendsto ξ hξ)
  simpa only [he, Complex.ofReal_one, mul_one, Function.comp_apply] using
    hh.const_mul (R3PressureFourier.rieszSymbol i j ξ)

end NavierStokes.R3RieszKernel
