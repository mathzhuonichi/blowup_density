import NavierStokes.R3CompactIntegration
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Actual integrability and monotonicity of Fourier Sobolev weights

These estimates apply to a Fourier profile once its boundedness and square
integrability have been supplied. They explicitly separate the unit ball around
zero from the high-frequency region. No identification of a Fourier normalization
or of the full Bochner force space is implicit.
-/

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory Set NavierStokes.ProblemStatement

/-- Inhomogeneous squared Sobolev integrand of a complex Fourier profile. -/
def besselIntegrand (s : ℝ) (φ : Space → ℂ) (ξ : Space) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ s * ‖φ ξ‖ ^ 2

/-- The inhomogeneous weights are monotone in their Sobolev order. -/
theorem besselIntegrand_mono {s r : ℝ} (hsr : s ≤ r) (φ : Space → ℂ) (ξ : Space) :
    besselIntegrand s φ ξ ≤ besselIntegrand r φ ξ := by
  apply mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) hsr)
  exact sq_nonneg _

/-- Lower-order inhomogeneous weighted integrals are finite whenever a
higher-order weighted integral is finite. -/
theorem integrable_besselIntegrand_mono {s r : ℝ} (hsr : s ≤ r)
    {φ : Space → ℂ} (hφ : Continuous φ) (hr : Integrable (besselIntegrand r φ)) :
    Integrable (besselIntegrand s φ) := by
  have hc : Continuous (besselIntegrand s φ) := by
    apply Continuous.mul
    · apply Continuous.rpow_const (continuous_const.add (continuous_norm.pow 2))
      intro ξ
      left
      exact ne_of_gt (by dsimp; positivity)
    · exact hφ.norm.pow 2
  apply hr.mono' hc.aestronglyMeasurable
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold besselIntegrand; positivity)]
  exact besselIntegrand_mono hsr φ ξ

theorem integral_besselIntegrand_mono {s r : ℝ} (hsr : s ≤ r)
    {φ : Space → ℂ} (hφ : Continuous φ) (hr : Integrable (besselIntegrand r φ)) :
    (∫ ξ, besselIntegrand s φ ξ) ≤ ∫ ξ, besselIntegrand r φ ξ :=
  integral_mono (integrable_besselIntegrand_mono hsr hφ hr) hr (besselIntegrand_mono hsr φ)

/-- The low-frequency homogeneous weighted square is integrable exactly in the
sufficient range required by insertion: bounded profiles and `s > -3/2`. -/
theorem homogeneous_low_frequency_integrable {s C : ℝ} (hs : -3 / 2 < s)
    {φ : Space → ℂ} (hφ : Measurable φ) (hC : 0 ≤ C) (hbound : ∀ ξ, ‖φ ξ‖ ≤ C) :
    IntegrableOn (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2) (Metric.ball 0 1) := by
  apply integrableOn_ball_of_norm_le_rpow (C := C ^ 2) (α := -(2 * s))
    (by simp [Space]) (by simp [Space]; linarith)
  · filter_upwards [] with ξ
    rw [neg_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : ‖φ ξ‖ ^ 2 ≤ C ^ 2 := sq_le_sq₀ (norm_nonneg _) hC |>.mpr (hbound ξ)
    nlinarith [Real.rpow_nonneg (norm_nonneg ξ) (2 * s)]
  · apply Measurable.aestronglyMeasurable
    fun_prop

/-- Bounded square-integrable profiles have finite homogeneous weighted energy
for `-3/2 < s ≤ 0`; this is the low-frequency gap in negative-order scaling. -/
theorem homogeneous_negative_integrable {s C : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0)
    {φ : Space → ℂ} (hφ : Measurable φ) (hC : 0 ≤ C) (hbound : ∀ ξ, ‖φ ξ‖ ≤ C)
    (hL2 : Integrable (fun ξ => ‖φ ξ‖ ^ 2)) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2) := by
  have hlo := homogeneous_low_frequency_integrable hs hφ hC hbound
  have hhi : IntegrableOn (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2)
      (Metric.ball 0 1)ᶜ := by
    apply hL2.integrableOn.mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [self_mem_ae_restrict (Metric.isOpen_ball.measurableSet.compl)] with ξ hξ
      have hn : 1 ≤ ‖ξ‖ := by simpa using hξ
      have hw := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith : 2 * s ≤ 0)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg ‖φ ξ‖]
  have h := integrableOn_union.mpr ⟨hlo, hhi⟩
  simpa using h

/-- Exact spatial scaling of the actual homogeneous weighted profile integral. -/
theorem homogeneous_energy_dilate (s k : ℝ) (hk : 0 < k) (φ : Space → ℂ) :
    (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖φ (k • ξ)‖ ^ 2) =
      k ^ (-(2 * s)) * (k ^ 3)⁻¹ * ∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2 := by
  have heq (ξ : Space) : ‖ξ‖ ^ (2 * s) * ‖φ (k • ξ)‖ ^ 2 =
      k ^ (-(2 * s)) * (‖k • ξ‖ ^ (2 * s) * ‖φ (k • ξ)‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk,
      Real.mul_rpow hk.le (norm_nonneg ξ), Real.rpow_neg hk.le]
    have hn : k ^ (2 * s) ≠ 0 := (Real.rpow_pos_of_pos hk _).ne'
    field_simp
  simp_rw [heq]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume
      (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2) k (hR := hk.le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  ring

end NSFormalization.Paper3
