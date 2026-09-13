import NavierStokes.ComparatorR3Bridge
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The integrable commutator majorant in the whole-space comparison

The manuscript's pressure commutator is bounded by a constant times
`|x|⁻³ min (|x| / R) 1`. Its `4/3` moment scales as `R⁻¹` in
three dimensions. This file proves integrability and that exact scaling;
identifying the Riesz-transform commutator with its kernel is separate.
-/

noncomputable section

namespace NavierStokes.R3PressureKernel

open Set MeasureTheory ProblemStatement
open scoped ENNReal

def baseKernel (x : Space) : ℝ :=
  if ‖x‖ < 1 then ‖x‖ ^ (-2 : ℝ) else ‖x‖ ^ (-3 : ℝ)

def baseMoment (x : Space) : ℝ :=
  if ‖x‖ < 1 then ‖x‖ ^ (-8 / 3 : ℝ) else ‖x‖ ^ (-4 : ℝ)

theorem baseKernel_nonneg (x : Space) : 0 ≤ baseKernel x := by
  unfold baseKernel
  split <;> positivity

theorem baseMoment_eq (x : Space) : baseKernel x ^ (4 / 3 : ℝ) = baseMoment x := by
  unfold baseKernel baseMoment
  split <;> rw [← Real.rpow_mul (norm_nonneg x)] <;> norm_num

theorem baseMoment_integrable : Integrable baseMoment := by
  change Integrable (fun x : Space =>
    if ‖x‖ < 1 then ‖x‖ ^ (-8 / 3 : ℝ) else ‖x‖ ^ (-4 : ℝ))
  apply (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r => if r < 1 then r ^ (-8 / 3 : ℝ) else r ^ (-4 : ℝ))).mpr
  have hnear : IntegrableOn (fun r : ℝ => r ^ (-2 / 3 : ℝ)) (Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)]
    norm_num
  have hfar : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Ici 1) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num))
  have hnear' : IntegrableOn
      (fun r : ℝ => r ^ (Module.finrank ℝ Space - 1) •
        (if r < 1 then r ^ (-8 / 3 : ℝ) else r ^ (-4 : ℝ))) (Ioo 0 1) := by
    apply hnear.congr_fun _ measurableSet_Ioo
    intro r hr
    simp only [ite_eq_left hr.2, smul_eq_mul]
    norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_add hr.1]
    norm_num
  have hfar' : IntegrableOn
      (fun r : ℝ => r ^ (Module.finrank ℝ Space - 1) •
        (if r < 1 then r ^ (-8 / 3 : ℝ) else r ^ (-4 : ℝ))) (Ici 1) := by
    apply hfar.congr_fun _ measurableSet_Ici
    intro r hr
    change 1 ≤ r at hr
    simp only [ite_eq_right (not_lt.mpr hr), smul_eq_mul]
    norm_num
    field_simp
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

def kernel (R : ℝ) (x : Space) : ℝ := R ^ (-3 : ℝ) * baseKernel (R⁻¹ • x)

theorem kernel_eq_majorant {R : ℝ} (hR : 0 < R) (x : Space) :
    kernel R x = ‖x‖ ^ (-3 : ℝ) * min (‖x‖ / R) 1 := by
  by_cases hx : x = 0
  · simp [kernel, baseKernel, hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp only [kernel, baseKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  by_cases hr : ‖x‖ < R
  · have hi : R⁻¹ * ‖x‖ < 1 := by
      rw [inv_mul_lt_iff₀ hR]
      simpa using hr
    rw [ite_eq_left hi, min_eq_left ((div_le_one hR).mpr hr.le)]
    norm_num
    field_simp
  · have hi : ¬ R⁻¹ * ‖x‖ < 1 := by
      rw [inv_mul_lt_iff₀ hR]
      simpa using hr
    rw [ite_eq_right hi, min_eq_right ((one_le_div hR).mpr (not_lt.mp hr))]
    norm_num
    field_simp

theorem kernel_nonneg {R : ℝ} (hR : 0 < R) (x : Space) : 0 ≤ kernel R x :=
  mul_nonneg (Real.rpow_nonneg hR.le _) (baseKernel_nonneg _)

theorem kernel_moment {R : ℝ} (hR : 0 < R) (x : Space) :
    kernel R x ^ (4 / 3 : ℝ) = R ^ (-4 : ℝ) * baseMoment (R⁻¹ • x) := by
  rw [kernel, Real.mul_rpow (Real.rpow_nonneg hR.le _) (baseKernel_nonneg _),
    ← Real.rpow_mul hR.le, baseMoment_eq]
  norm_num

theorem kernel_moment_integrable {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Space => kernel R x ^ (4 / 3 : ℝ)) := by
  simp_rw [kernel_moment hR]
  exact (baseMoment_integrable.comp_smul (inv_ne_zero hR.ne')).const_mul _

/-- This is the `R⁻¹` fourth-thirds moment bound in equation
`global:kernel-bound`, with an exact constant independent of `R`. -/
theorem integral_kernel_moment {R : ℝ} (hR : 0 < R) :
    (∫ x : Space, kernel R x ^ (4 / 3 : ℝ)) = R⁻¹ * (∫ x : Space, baseMoment x) := by
  simp_rw [kernel_moment hR]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume baseMoment hR.le]
  simp only [smul_eq_mul]
  norm_num
  field_simp

theorem kernel_measurable (R : ℝ) : Measurable (kernel R) := by
  unfold kernel baseKernel
  apply measurable_const.mul
  exact Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

theorem kernel_memLp {R : ℝ} (hR : 0 < R) : MemLp (kernel R) (4 / 3) := by
  apply (integrable_norm_rpow_iff (kernel_measurable R).aestronglyMeasurable
    (by norm_num : (4 / 3 : ℝ≥0∞) ≠ 0) (by finiteness : (4 / 3 : ℝ≥0∞) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (kernel_nonneg hR _)] using kernel_moment_integrable hR

/-- The commutator majorant has precisely the required `R⁻³⁄⁴` norm. -/
theorem kernel_lpNorm {R : ℝ} (hR : 0 < R) :
    lpNorm (kernel R) (4 / 3) volume =
      R ^ (-3 / 4 : ℝ) * (∫ x : Space, baseMoment x) ^ (3 / 4 : ℝ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by finiteness)
    (kernel_measurable R).aestronglyMeasurable]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (kernel_nonneg hR _)]
  rw [integral_kernel_moment hR, Real.mul_rpow (inv_nonneg.mpr hR.le)
    (integral_nonneg (fun x => by
      rw [← baseMoment_eq]
      exact Real.rpow_nonneg (baseKernel_nonneg x) _))]
  norm_num
  rw [Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]
  simp

/-- A refined cutoff difference for an `L²` pressure decomposition. The
first term keeps five powers of the cutoff at the integration variable;
the second has enough powers of the distance to be locally square integrable
after multiplication by the Riesz kernel. -/
theorem power_six_difference {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hab : |a - b| ≤ d) : |a ^ 6 - b ^ 6| ≤ 96 * (d * b ^ 5 + d ^ 6) := by
  have hmax : max |a| |b| ≤ b + d := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    apply max_le
    · linarith [le_abs_self (a - b)]
    · linarith
  calc
    |a ^ 6 - b ^ 6| ≤ |a - b| * 6 * max |a| |b| ^ (6 - 1) := abs_pow_sub_pow_le a b 6
    _ ≤ d * 6 * (b + d) ^ 5 := by
      norm_num
      gcongr
    _ ≤ d * 6 * (2 ^ (5 - 1) * (b ^ 5 + d ^ 5)) :=
      mul_le_mul_of_nonneg_left (add_pow_le hb hd 5) (by positivity)
    _ = 96 * (d * b ^ 5 + d ^ 6) := by ring

end NavierStokes.R3PressureKernel
