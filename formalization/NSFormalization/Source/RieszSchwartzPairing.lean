import NSFormalization.Source.RieszGaussianMixture
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section
namespace NSFormalization.Source.RieszSchwartzPairing
open Set MeasureTheory NavierStokes.ProblemStatement

/-- The actual Riesz kernel is absolutely integrable against every Schwartz test. -/
theorem riesz_schwartz_integrable {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : SchwartzMap Space ℂ) :
    Integrable (fun x : Space => ‖x‖ ^ (a - 3) * ‖φ x‖) := by
  have hm : Measurable (fun x : Space => ‖x‖ ^ (a - 3) * ‖φ x‖) := by fun_prop
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  have hnear : IntegrableOn (fun x : Space => ‖x‖ ^ (a - 3) * ‖φ x‖)
      (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by omega : 1 ≤ Module.finrank ℝ Space)
      (C := SchwartzMap.seminorm ℝ 0 0 φ) (α := 3-a)
    · rw [hd]; exact_mod_cast (by linarith : 3-a < 3)
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_sub]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (SchwartzMap.norm_le_seminorm ℝ φ x) (Real.rpow_nonneg (norm_nonneg x) _)
    · exact hm.aestronglyMeasurable
  have hfar : IntegrableOn (fun x : Space => ‖x‖ ^ (a - 3) * ‖φ x‖)
      (Metric.ball 0 1)ᶜ := by
    apply φ.integrable.norm.integrableOn.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    have hx1 : 1 ≤ ‖x‖ := by simpa using hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith))
  simpa using (integrableOn_union.mpr ⟨hnear, hfar⟩)

open NSFormalization.Source.RieszGaussianMixture
open NavierStokes.R3GaussianPressure

/-- Positive scales have a nonnegative real density. -/
theorem density_nonneg {a t : ℝ} (ha3 : a < 3) (ht : 0 < t) (x : Space) :
    0 ≤ scaleWeight a t * gaussianReal t x := by
  unfold scaleWeight
  have hG := Real.Gamma_pos_of_pos (show 0 < (3-a)/2 by linarith)
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hG.le) (Real.rpow_nonneg ht.le _))
    (gaussianReal_pos t x).le

/-- Absolute joint integrability for the full positive-scale Schwartz pairing. -/
theorem scale_schwartz_integrable {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : SchwartzMap Space ℂ) :
    Integrable (fun p : ℝ × Space => scaleDensity a p.1 p.2 * φ p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hm : Measurable (fun p : ℝ × Space => scaleDensity a p.1 p.2 * φ p.2) := by
    unfold scaleDensity scaleWeight gaussian gaussianReal
    fun_prop
  have he (x : Space) :
      (fun t : ℝ => ‖scaleDensity a t x * φ x‖) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => (scaleWeight a t * gaussianReal t x) * ‖φ x‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul]
    have h : ‖scaleDensity a t x‖ = scaleWeight a t * gaussianReal t x := by
      rw [scaleDensity, gaussian, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (density_nonneg ha3 ht x)]
    rw [h]
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [volume.ae_ne (0 : Space)] with x hx
    apply (integrable_norm_iff (show AEStronglyMeasurable (fun t => scaleDensity a t x * φ x) (volume.restrict (Ioi 0)) from (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)).mp
    exact ((scale_integrable ha3 hx).mul_const ‖φ x‖).congr (he x).symm
  · apply (riesz_schwartz_integrable ha ha3 φ).congr
    filter_upwards [volume.ae_ne (0 : Space)] with x hx
    rw [integral_congr_ae (he x), integral_mul_const, integral_scaleDensity_real ha3 hx]

/-- The full Gaussian mixture agrees with the Riesz kernel in Schwartz pairing. -/
theorem integral_scale_schwartz {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : SchwartzMap Space ℂ) :
    (∫ t : ℝ in Ioi 0, ∫ x : Space, scaleDensity a t x * φ x) =
      ∫ x : Space, ((‖x‖ ^ (a - 3) : ℝ) : ℂ) * φ x := by
  rw [integral_integral_swap (scale_schwartz_integrable ha ha3 φ)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : Space)] with x hx
  rw [integral_mul_const]
  have h : (∫ t : ℝ in Ioi 0, scaleDensity a t x) = ((‖x‖ ^ (a - 3) : ℝ) : ℂ) := by
    simp only [scaleDensity, gaussian, ← Complex.ofReal_mul]
    rw [integral_complex_ofReal, integral_scaleDensity_real ha3 hx]
  rw [h]

end NSFormalization.Source.RieszSchwartzPairing
