import NavierStokes.R3PressureKernel

/-!
# The two kernels in the refined pressure commutator estimate

For the sixth-power cutoff, the near term has kernel
`R⁻¹ |x|⁻² 1_{|x|<R}` in `L^(6/5)`, while the remainder has
kernel `R⁻⁶ |x|³` inside the ball and `|x|⁻³` outside it, in `L²`.
Their norms scale as `R⁻¹⁄²` and `R⁻³⁄²`, respectively.
-/

noncomputable section

namespace NavierStokes.R3PressureNearKernel

open Set Filter MeasureTheory ProblemStatement
open scoped ENNReal

def radialProfile (a b : ℝ) (x : Space) : ℝ :=
  if ‖x‖ < 1 then ‖x‖ ^ a else ‖x‖ ^ b

theorem radialProfile_nonneg (a b : ℝ) (x : Space) : 0 ≤ radialProfile a b x := by
  unfold radialProfile
  split <;> positivity

theorem radialProfile_measurable (a b : ℝ) : Measurable (radialProfile a b) := by
  unfold radialProfile
  exact Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

theorem radialProfile_integrable {a b : ℝ} (ha : -3 < a) (hb : b < -3) :
    Integrable (radialProfile a b) := by
  apply (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r => if r < 1 then r ^ a else r ^ b)).mpr
  have hnear : IntegrableOn (fun r : ℝ => r ^ (2 + a)) (Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)]
    linarith
  have hfar : IntegrableOn (fun r : ℝ => r ^ (2 + b)) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num))
  have hnear' : IntegrableOn (fun r : ℝ => r ^ (Module.finrank ℝ Space - 1) •
      (if r < 1 then r ^ a else r ^ b)) (Ioo 0 1) := by
    apply hnear.congr_fun _ measurableSet_Ioo
    intro r hr
    simp only [ite_eq_left hr.2, smul_eq_mul]
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub]
    rw [← Real.rpow_natCast, ← Real.rpow_add hr.1]
    norm_num
  have hfar' : IntegrableOn (fun r : ℝ => r ^ (Module.finrank ℝ Space - 1) •
      (if r < 1 then r ^ a else r ^ b)) (Ici 1) := by
    apply hfar.congr_fun _ measurableSet_Ici
    intro r hr
    change 1 ≤ r at hr
    simp only [ite_eq_right (not_lt.mpr hr), smul_eq_mul]
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub]
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith : 0 < r)]
    norm_num
  have hsets : Ioo (0 : ℝ) 1 ∪ Ici 1 = Ioi 0 := by
    ext r
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hr : r < 1
      · exact Or.inl ⟨h, hr⟩
      · exact Or.inr (not_lt.mp hr)
  simpa only [hsets] using hnear'.union hfar'

def scaled (R : ℝ) (f : Space → ℝ) (x : Space) : ℝ := R ^ (-3 : ℝ) * f (R⁻¹ • x)

theorem scaled_nonneg {R : ℝ} (hR : 0 < R) {f : Space → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Space) :
    0 ≤ scaled R f x := mul_nonneg (Real.rpow_nonneg hR.le _) (hf _)

theorem scaled_measurable (R : ℝ) {f : Space → ℝ} (hf : Measurable f) :
    Measurable (scaled R f) := by
  unfold scaled
  fun_prop

theorem scaled_power {R p : ℝ} (hR : 0 < R) {f : Space → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Space) :
    scaled R f x ^ p = R ^ (-3 * p) * f (R⁻¹ • x) ^ p := by
  rw [scaled, Real.mul_rpow (Real.rpow_nonneg hR.le _) (hf _), ← Real.rpow_mul hR.le]

theorem scaled_power_integrable {R p : ℝ} (hR : 0 < R) {f : Space → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hi : Integrable (fun x : Space => f x ^ p)) :
    Integrable (fun x : Space => scaled R f x ^ p) := by
  simp_rw [scaled_power hR hf]
  exact (hi.comp_smul (inv_ne_zero hR.ne')).const_mul _

theorem integral_scaled_power {R p : ℝ} (hR : 0 < R) {f : Space → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (∫ x : Space, scaled R f x ^ p) = R ^ (-3 * p + 3) * (∫ x : Space, f x ^ p) := by
  simp_rw [scaled_power hR hf]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Space => f x ^ p) hR.le]
  simp only [smul_eq_mul]
  norm_num only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← mul_assoc, ← Real.rpow_natCast R 3, ← Real.rpow_add hR]
  norm_num

theorem scaled_memLp {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ⊤)
    {f : Space → ℝ} (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) (hi : MemLp f p) :
    MemLp (scaled R f) p := by
  apply (integrable_norm_rpow_iff (scaled_measurable R hf).aestronglyMeasurable hp hpt).mp
  have hb := (integrable_norm_rpow_iff hf.aestronglyMeasurable hp hpt).mpr hi
  simp only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] at hb
  simpa only [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg hR hpos _)] using
    scaled_power_integrable hR hpos hb

theorem scaled_lpNorm {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ⊤)
    {f : Space → ℝ} (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) :
    lpNorm (scaled R f) p volume = R ^ (-3 + 3 / p.toReal) * lpNorm f p volume := by
  rw [lpNorm_eq_integral_norm_rpow_toReal hp hpt (scaled_measurable R hf).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal hp hpt hf.aestronglyMeasurable]
  simp only [Real.norm_eq_abs, abs_of_nonneg (hpos _), abs_of_nonneg (scaled_nonneg hR hpos _)]
  rw [integral_scaled_power hR hpos, Real.mul_rpow (Real.rpow_nonneg hR.le _)
    (integral_nonneg (fun x => Real.rpow_nonneg (hpos x) _)), ← Real.rpow_mul hR.le]
  congr 1
  congr 1
  have hpn : p.toReal ≠ 0 := (ENNReal.toReal_pos hp hpt).ne'
  field_simp

def nearBase (x : Space) : ℝ := if ‖x‖ < 1 then ‖x‖ ^ (-2 : ℝ) else 0

def remainderBase : Space → ℝ := radialProfile 3 (-3)

theorem nearBase_nonneg (x : Space) : 0 ≤ nearBase x := by
  unfold nearBase
  split <;> positivity

theorem nearBase_measurable : Measurable nearBase := by
  unfold nearBase
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

theorem nearBase_power_integrable : Integrable (fun x : Space => nearBase x ^ (6 / 5 : ℝ)) := by
  apply (radialProfile_integrable (a := -12 / 5) (b := -4) (by norm_num) (by norm_num)).mono'
    (nearBase_measurable.pow_const _).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (nearBase_nonneg x) _)]
  unfold nearBase radialProfile
  split
  · rw [← Real.rpow_mul (norm_nonneg x)]
    norm_num
  · simp only [Real.zero_rpow (by norm_num : (6 / 5 : ℝ) ≠ 0)]
    positivity

theorem remainderBase_power_integrable : Integrable (fun x : Space => remainderBase x ^ (2 : ℝ)) := by
  apply (radialProfile_integrable (a := 6) (b := -6) (by norm_num) (by norm_num)).congr
  filter_upwards with x
  unfold remainderBase radialProfile
  split <;> rw [← Real.rpow_mul (norm_nonneg x)] <;> norm_num

theorem nearBase_memLp : MemLp nearBase (6 / 5) := by
  apply (integrable_norm_rpow_iff nearBase_measurable.aestronglyMeasurable
    (by norm_num : (6 / 5 : ℝ≥0∞) ≠ 0) (by finiteness : (6 / 5 : ℝ≥0∞) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (nearBase_nonneg _)] using nearBase_power_integrable

theorem remainderBase_memLp : MemLp remainderBase 2 := by
  apply (integrable_norm_rpow_iff (radialProfile_measurable 3 (-3)).aestronglyMeasurable
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp
  simpa only [remainderBase, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (radialProfile_nonneg 3 (-3) _)] using remainderBase_power_integrable

def nearKernel (R : ℝ) : Space → ℝ := scaled R nearBase

def remainderKernel (R : ℝ) : Space → ℝ := scaled R remainderBase

theorem nearKernel_memLp {R : ℝ} (hR : 0 < R) : MemLp (nearKernel R) (6 / 5) :=
  scaled_memLp hR (by norm_num) (by finiteness) nearBase_measurable nearBase_nonneg nearBase_memLp

theorem remainderKernel_memLp {R : ℝ} (hR : 0 < R) : MemLp (remainderKernel R) 2 :=
  scaled_memLp hR (by norm_num) (by norm_num) (radialProfile_measurable 3 (-3))
    (radialProfile_nonneg 3 (-3)) remainderBase_memLp

theorem nearKernel_lpNorm {R : ℝ} (hR : 0 < R) :
    lpNorm (nearKernel R) (6 / 5) volume =
      R ^ (-1 / 2 : ℝ) * lpNorm nearBase (6 / 5) volume := by
  have h := scaled_lpNorm hR (p := 6 / 5) (by norm_num) (by finiteness)
    nearBase_measurable nearBase_nonneg
  norm_num at h
  simpa only [nearKernel, neg_div] using h

theorem remainderKernel_lpNorm {R : ℝ} (hR : 0 < R) :
    lpNorm (remainderKernel R) 2 volume =
      R ^ (-3 / 2 : ℝ) * lpNorm remainderBase 2 volume := by
  have h := scaled_lpNorm hR (p := 2) (by norm_num) (by norm_num)
    (radialProfile_measurable 3 (-3)) (radialProfile_nonneg 3 (-3))
  norm_num at h
  simpa only [remainderKernel, remainderBase, neg_div] using h

theorem nearKernel_eq {R : ℝ} (hR : 0 < R) (x : Space) :
    nearKernel R x = if ‖x‖ < R then R⁻¹ * ‖x‖ ^ (-2 : ℝ) else 0 := by
  by_cases hx : x = 0
  · simp [nearKernel, scaled, nearBase, hx, hR]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp only [nearKernel, scaled, nearBase, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  have hi : R⁻¹ * ‖x‖ < 1 ↔ ‖x‖ < R := by rw [inv_mul_lt_iff₀ hR, mul_one]
  by_cases hr : ‖x‖ < R
  · rw [ite_eq_left (hi.mpr hr), ite_eq_left hr]
    norm_num
    field_simp
  · rw [ite_eq_right (fun h => hr (hi.mp h)), ite_eq_right hr, mul_zero]

theorem remainderKernel_eq {R : ℝ} (hR : 0 < R) (x : Space) :
    remainderKernel R x =
      if ‖x‖ < R then R ^ (-6 : ℝ) * ‖x‖ ^ 3 else ‖x‖ ^ (-3 : ℝ) := by
  by_cases hx : x = 0
  · simp [remainderKernel, scaled, remainderBase, radialProfile, hx, hR]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp only [remainderKernel, scaled, remainderBase, radialProfile, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  have hi : R⁻¹ * ‖x‖ < 1 ↔ ‖x‖ < R := by rw [inv_mul_lt_iff₀ hR, mul_one]
  by_cases hr : ‖x‖ < R
  · rw [ite_eq_left (hi.mpr hr), ite_eq_left hr]
    norm_num
    field_simp
  · rw [ite_eq_right (fun h => hr (hi.mp h)), ite_eq_right hr]
    norm_num
    field_simp

theorem sixth_power_difference {a b L d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hL : 1 ≤ L) (hd : 0 ≤ d) (hab : |a - b| ≤ L * d) :
    |a ^ 6 - b ^ 6| ≤ 96 * L ^ 6 * (d * b ^ 5 + d ^ 6) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hL5 : 1 ≤ L ^ 5 := by
    calc
      1 = (1 : ℝ) ^ 5 := by norm_num
      _ ≤ L ^ 5 := by gcongr
  have hLself : L ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_left hL5 hL0
    simpa only [mul_one, ← pow_succ'] using h
  calc
    _ ≤ 96 * (L * d * b ^ 5 + L ^ 6 * d ^ 6) := by
      simpa only [mul_pow] using
        R3PressureKernel.power_six_difference ha hb (mul_nonneg hL0 hd) hab
    _ ≤ 96 * (L ^ 6 * d * b ^ 5 + L ^ 6 * d ^ 6) := by gcongr
    _ = _ := by ring

/-- Pointwise domination of a sixth-power cutoff commutator by the two
kernels whose Young convolution bounds give an `L²` estimate. -/
theorem cutoff_kernel_bound {R L a b : ℝ} (hR : 0 < R) (hL : 1 ≤ L)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (x : Space)
    (hab : |a - b| ≤ L * (‖x‖ / R)) :
    ‖x‖ ^ (-3 : ℝ) * |a ^ 6 - b ^ 6| ≤
      (96 * L ^ 6) * (nearKernel R x * b ^ 5 + remainderKernel R x) := by
  by_cases hx : x = 0
  · simp [nearKernel_eq hR, remainderKernel_eq hR, hx, hR]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [nearKernel_eq hR, remainderKernel_eq hR]
  by_cases hr : ‖x‖ < R
  · rw [ite_eq_left hr, ite_eq_left hr]
    have hh := sixth_power_difference ha.1 hb.1 hL (div_nonneg (norm_nonneg x) hR.le) hab
    calc
      _ ≤ ‖x‖ ^ (-3 : ℝ) * ((96 * L ^ 6) *
          ((‖x‖ / R) * b ^ 5 + (‖x‖ / R) ^ 6)) :=
        mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (norm_nonneg x) _)
      _ = _ := by
        norm_num
        field_simp
  · rw [ite_eq_right hr, ite_eq_right hr, zero_mul, zero_add]
    have habs : |a ^ 6 - b ^ 6| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [pow_le_one₀ ha.1 ha.2 (n := 6),
        pow_le_one₀ hb.1 hb.2 (n := 6), pow_nonneg ha.1 6, pow_nonneg hb.1 6]
    have hL6 : 1 ≤ L ^ 6 := by
      calc
        1 = (1 : ℝ) ^ 6 := by norm_num
        _ ≤ L ^ 6 := by gcongr
    have hc : 1 ≤ 96 * L ^ 6 := by linarith
    calc
      _ ≤ ‖x‖ ^ (-3 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg (norm_nonneg x) _)
      _ = 1 * ‖x‖ ^ (-3 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (norm_nonneg x) _)

end NavierStokes.R3PressureNearKernel
