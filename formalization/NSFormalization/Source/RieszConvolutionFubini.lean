import NSFormalization.Source.RieszSchwartzPairing
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
namespace NSFormalization.Source.RieszConvolutionFubini
open Set MeasureTheory NavierStokes.ProblemStatement

/-- The actual Riesz convolution integrand is jointly absolutely integrable against
any pair of Schwartz functions, for every order strictly between zero and three. -/
theorem kernel_convolution_test_integrable {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (g h : SchwartzMap Space ℂ) :
    Integrable (fun p : Space × Space =>
      ((‖p.2‖ ^ (a - 3) : ℝ) : ℂ) * g (p.1 - p.2) * h p.1)
      (volume.prod volume) := by
  let K : Space → ℝ := (Metric.ball 0 1).indicator (fun y => ‖y‖ ^ (a - 3))
  let M := SchwartzMap.seminorm ℝ 0 0 g
  have hK : Integrable K := by
    apply (integrable_indicator_iff measurableSet_ball).mpr
    apply integrableOn_ball_of_norm_le_rpow (by simp [Space] : 1 ≤ Module.finrank ℝ Space)
      (C := 1) (α := 3-a)
    · have hd : Module.finrank ℝ Space = 3 := by simp [Space]
      rw [hd]
      exact_mod_cast (by linarith : 3-a < 3)
    · filter_upwards with y
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _), neg_sub]
    · exact (by fun_prop : Measurable (fun y : Space => ‖y‖ ^ (a-3))).aestronglyMeasurable
  have hplain : Integrable (fun p : Space × Space => ‖g (p.1-p.2)‖ * ‖h p.1‖)
      (volume.prod volume) := by
    apply (integrable_prod_iff (by fun_prop)).mpr
    constructor
    · filter_upwards with x
      exact ((volume.measurePreserving_sub_left x).integrable_comp_of_integrable g.integrable.norm).mul_const _
    · have he (x : Space) : (∫ y : Space, ‖‖g (x-y)‖ * ‖h x‖‖) =
          (∫ y : Space, ‖g y‖) * ‖h x‖ := by
        simp only [norm_mul, norm_norm, integral_mul_const]
        rw [show (∫ y : Space, ‖g (x-y)‖) = ∫ y : Space, ‖g y‖ from
          integral_sub_left_eq_self (fun y : Space => ‖g y‖) volume x]
      simp_rw [he]
      exact h.integrable.norm.const_mul _
  have hmajor : Integrable (fun p : Space × Space =>
      M * K p.2 * ‖h p.1‖ + ‖g (p.1-p.2)‖ * ‖h p.1‖) (volume.prod volume) := by
    have hh : Integrable (fun x : Space => ‖h x‖) volume := h.integrable.norm
    have hp := hh.mul_prod (hK.const_mul M)
    have hp' : Integrable (fun p : Space × Space => M * K p.2 * ‖h p.1‖)
        (volume.prod volume) := by simpa only [mul_comm] using hp
    exact hp'.add hplain
  have hm : Measurable (fun p : Space × Space =>
      ((‖p.2‖ ^ (a - 3) : ℝ) : ℂ) * g (p.1 - p.2) * h p.1) := by fun_prop
  apply hmajor.mono' hm.aestronglyMeasurable
  filter_upwards with p
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg p.2) _)]
  have hM : ‖g (p.1-p.2)‖ ≤ M := SchwartzMap.norm_le_seminorm ℝ g _
  by_cases hy : p.2 ∈ Metric.ball (0 : Space) 1
  · simp only [K, indicator_of_mem hy]
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg (norm_nonneg p.2) (a-3)))
      (norm_nonneg (h p.1))
    nlinarith [mul_nonneg (norm_nonneg (g (p.1-p.2))) (norm_nonneg (h p.1))]
  · simp only [K, indicator_of_notMem hy, mul_zero, zero_mul, zero_add]
    have hy1 : 1 ≤ ‖p.2‖ := by simpa using hy
    have hk := Real.rpow_le_one_of_one_le_of_nonpos hy1 (show a-3 ≤ 0 by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hk) (norm_nonneg _)

end NSFormalization.Source.RieszConvolutionFubini
