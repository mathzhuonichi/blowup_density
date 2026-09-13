import NSFormalization.Source.ParabolicScaling
import NSFormalization.Paper3.SobolevWeights
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Fourier scaling of one concentrated force

The Fourier transform here is Mathlib's standard transform with kernel
exp(-2*pi*i*x.xi). Spatial parabolic exponents do not depend on that fixed
normalization. The weighted energies in this module use that transform
explicitly; comparison with the manuscript's angular-frequency convention is
a separate fixed change of frequency variable.
-/

noncomputable section

namespace NSFormalization.Source

open NavierStokes.ProblemStatement MeasureTheory
open scoped FourierTransform RealInnerProductSpace

def concentratedForce (k : ℝ) (f : Space → ℂ) : Space → ℂ :=
  fun x => k ^ 3 • f (k • x)

theorem fourier_dilation (f : Space → ℂ) (k : ℝ) (hk : 0 < k) (ξ : Space) :
    𝓕 (fun x => f (k • x)) ξ = (k ^ 3)⁻¹ • 𝓕 f (k⁻¹ • ξ) := by
  let g : Space → ℂ := fun y => 𝐞 (-inner ℝ y (k⁻¹ • ξ)) • f y
  have he (x : Space) : g (k • x) = 𝐞 (-inner ℝ x ξ) • f (k • x) := by
    dsimp [g]
    congr 2
    simp [real_inner_smul_left, real_inner_smul_right, hk.ne']
  rw [Real.fourier_eq]
  simp_rw [← he]
  have h := Measure.integral_comp_smul_of_nonneg volume g k (hR := hk.le)
  simpa only [finrank_euclideanSpace, Fintype.card_fin, g, Real.fourier_eq] using h

/-- The cubic physical force amplitude cancels the spatial Fourier Jacobian. -/
theorem fourier_concentratedForce (f : Space → ℂ) (k : ℝ) (hk : 0 < k) (ξ : Space) :
    𝓕 (concentratedForce k f) ξ = 𝓕 f (k⁻¹ • ξ) := by
  have ha : 𝓕 (concentratedForce k f) ξ = k ^ 3 • 𝓕 (fun x => f (k • x)) ξ := by
    simp only [Real.fourier_eq, concentratedForce, smul_comm _ (k ^ 3), integral_smul]
  rw [ha, fourier_dilation f k hk ξ, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 3 hk.ne'), one_smul]

/-- Squared inhomogeneous Sobolev energy, with the Fourier convention stated
above. Integrability hypotheses are used whenever energies are compared. -/
def fourierSobolevSq (s : ℝ) (f : Space → ℂ) : ℝ :=
  ∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2

/-- The exact spatial change of variables behind all the force thresholds. -/
theorem fourierSobolevSq_concentrated (s : ℝ) (f : Space → ℂ)
    (k : ℝ) (hk : 0 < k) :
    fourierSobolevSq s (concentratedForce k f) =
      k ^ 3 * ∫ ξ : Space, (1 + k ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2 := by
  unfold fourierSobolevSq
  simp_rw [fourier_concentratedForce f k hk]
  let G : Space → ℝ := fun ξ => (1 + k ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2
  have he (ξ : Space) : G (k⁻¹ • ξ) =
      (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f (k⁻¹ • ξ)‖ ^ 2 := by
    dsimp [G]
    congr 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk), mul_pow]
    field_simp
  simp_rw [← he]
  rw [Measure.integral_comp_smul_of_nonneg volume G k⁻¹
    (hR := (inv_pos.mpr hk).le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv, smul_eq_mul, G]

theorem positive_weight_scale {s k r : ℝ} (hs : 0 ≤ s) (hk : 1 ≤ k) :
    (1 + k ^ 2 * r ^ 2) ^ s ≤ k ^ (2 * s) * (1 + r ^ 2) ^ s := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  calc
    (1 + k ^ 2 * r ^ 2) ^ s ≤ (k ^ 2 * (1 + r ^ 2)) ^ s := by
      apply Real.rpow_le_rpow (by positivity) _ hs
      nlinarith [sq_nonneg (k - 1)]
    _ = k ^ (2 * s) * (1 + r ^ 2) ^ s := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hk0.le]
      norm_num

/-- For negative orders, the homogeneous weight is a majorant away from the
single zero-frequency point. Its integrability is proved in SobolevWeights. -/
theorem negative_weight_scale {s k r : ℝ} (hs : s ≤ 0) (hk : 0 < k) (hr : 0 < r) :
    (1 + k ^ 2 * r ^ 2) ^ s ≤ k ^ (2 * s) * r ^ (2 * s) := by
  calc
    (1 + k ^ 2 * r ^ 2) ^ s ≤ (k ^ 2 * r ^ 2) ^ s := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hs
    _ = k ^ (2 * s) * r ^ (2 * s) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1 <;> rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] <;> norm_num

theorem scaled_bessel_continuous (s k : ℝ) {φ : Space → ℂ} (hφ : Continuous φ) :
    Continuous (fun ξ : Space => (1 + k ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖φ ξ‖ ^ 2) := by
  apply Continuous.mul
  · apply Continuous.rpow_const
      (continuous_const.add (continuous_const.mul (continuous_norm.pow 2)))
    intro ξ
    left
    exact ne_of_gt (by dsimp; positivity)
  · exact hφ.norm.pow 2

/-- Positive-order force concentration is bounded by the same inhomogeneous
Sobolev energy of the unscaled profile. -/
theorem fourierSobolevSq_concentrated_le_positive {s k : ℝ}
    (hs : 0 ≤ s) (hk : 1 ≤ k) (f : Space → ℂ)
    (hF : Continuous (𝓕 f))
    (hint : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2)) :
    fourierSobolevSq s (concentratedForce k f) ≤
      k ^ (3 + 2 * s) * fourierSobolevSq s f := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  let G : Space → ℝ := fun ξ => (1 + k ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2
  let H : Space → ℝ := fun ξ => k ^ (2 * s) *
    ((1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2)
  have hH : Integrable H := hint.const_mul _
  have hpoint (ξ : Space) : G ξ ≤ H ξ := by
    have h := mul_le_mul_of_nonneg_right (positive_weight_scale (r := ‖ξ‖) hs hk)
      (sq_nonneg ‖𝓕 f ξ‖)
    simpa only [G, H, mul_assoc] using h
  have hG : Integrable G := hH.mono' (scaled_bessel_continuous s k hF).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [G]; positivity)]
      exact hpoint ξ))
  rw [fourierSobolevSq_concentrated s f k hk0]
  have hbound := mul_le_mul_of_nonneg_left (integral_mono hG hH hpoint) (pow_nonneg hk0.le 3)
  have he : k ^ 3 * (∫ ξ, H ξ) = k ^ (3 + 2 * s) * fourierSobolevSq s f := by
    rw [show (∫ ξ, H ξ) = k ^ (2 * s) * fourierSobolevSq s f by
      exact integral_const_mul _ _]
    rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hk0]
    norm_num
  exact hbound.trans_eq he

/-- Negative-order force concentration is bounded by the finite homogeneous
weighted energy. The zero frequency is excluded only on a null set. -/
theorem fourierSobolevSq_concentrated_le_negative {s k : ℝ}
    (hs : s ≤ 0) (hk : 0 < k) (f : Space → ℂ)
    (hF : Continuous (𝓕 f))
    (hint : Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2)) :
    fourierSobolevSq s (concentratedForce k f) ≤
      k ^ (3 + 2 * s) * (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2) := by
  let G : Space → ℝ := fun ξ => (1 + k ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2
  let H : Space → ℝ := fun ξ => k ^ (2 * s) * (‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2)
  have hH : Integrable H := hint.const_mul _
  have hpoint : ∀ᵐ ξ : Space, G ξ ≤ H ξ := by
    filter_upwards [volume.ae_ne (0 : Space)] with ξ hξ
    have h := mul_le_mul_of_nonneg_right (negative_weight_scale hs hk (norm_pos_iff.mpr hξ))
      (sq_nonneg ‖𝓕 f ξ‖)
    simpa only [G, H, mul_assoc] using h
  have hG : Integrable G := hH.mono' (scaled_bessel_continuous s k hF).aestronglyMeasurable
    (hpoint.mono (fun ξ hξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [G]; positivity)]
      exact hξ))
  rw [fourierSobolevSq_concentrated s f k hk]
  have hbound := mul_le_mul_of_nonneg_left (integral_mono_ae hG hH hpoint) (pow_nonneg hk.le 3)
  have he : k ^ 3 * (∫ ξ, H ξ) =
      k ^ (3 + 2 * s) * (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2) := by
    rw [show (∫ ξ, H ξ) = k ^ (2 * s) *
        (∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2) by exact integral_const_mul _ _]
    rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hk]
    norm_num
  exact hbound.trans_eq he

end NSFormalization.Source
