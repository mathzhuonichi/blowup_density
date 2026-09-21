import NSFormalization.Source.BesselH2Fourier
import NSFormalization.Source.YoungConvolution
import Mathlib.Analysis.Fourier.Convolution

noncomputable section
open MeasureTheory Filter FourierTransform NavierStokes.ProblemStatement
open scoped ENNReal
namespace NSFormalization.Source.FourierTameProduct

/-- The actual pointwise product as a Schwartz function. -/
def schwartzProduct (φ ψ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ ψ

@[simp] theorem schwartzProduct_apply (φ ψ : SchwartzMap Space ℂ) (x : Space) :
    schwartzProduct φ ψ x = φ x * ψ x := rfl

/-- Fourier inversion converts the existing convolution theorem into the
product-to-convolution identity in the cycles convention. -/
theorem fourier_schwartzProduct (φ ψ : SchwartzMap Space ℂ) :
    𝓕 (schwartzProduct φ ψ) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 φ) (𝓕 ψ) := by
  let C := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 φ) (𝓕 ψ)
  have h : 𝓕⁻ C = schwartzProduct φ ψ := by
    ext x
    change 𝓕 C (-x) = φ x * ψ x
    rw [SchwartzMap.fourier_convolution]
    change 𝓕 (𝓕 φ) (-x) * 𝓕 (𝓕 ψ) (-x) = φ x * ψ x
    change 𝓕⁻ (𝓕 φ) x * 𝓕⁻ (𝓕 ψ) x = φ x * ψ x
    simp
  rw [← h, FourierTransform.fourier_fourierInv_eq]

/-- The Fourier transform of the actual product is the actual convolution
integral, at every frequency. -/
theorem fourier_schwartzProduct_apply (φ ψ : SchwartzMap Space ℂ) (ξ : Space) :
    𝓕 (schwartzProduct φ ψ) ξ =
      ∫ η : Space, 𝓕 φ η * 𝓕 ψ (ξ - η) := by
  rw [fourier_schwartzProduct, SchwartzMap.convolution_apply]
  rfl

/-- The Bessel weight used by the weighted Fourier L2 realization. -/
def besselWeight (m : ℕ) (x : Space) : ℝ := (1 + ‖x‖ ^ 2) ^ ((m : ℝ) / 2)

theorem besselWeight_eq_sqrt_pow (m : ℕ) (x : Space) :
    besselWeight m x = Real.sqrt (1 + ‖x‖ ^ 2) ^ m := by
  rw [besselWeight, Real.rpow_div_two_eq_sqrt _ (by positivity), Real.rpow_natCast]

theorem besselWeight_nonneg (m : ℕ) (x : Space) : 0 ≤ besselWeight m x := by
  unfold besselWeight
  positivity

/-- The Japanese bracket is subadditive. -/
theorem sqrt_bessel_add_le (x y : Space) :
    Real.sqrt (1 + ‖x + y‖ ^ 2) ≤
      Real.sqrt (1 + ‖x‖ ^ 2) + Real.sqrt (1 + ‖y‖ ^ 2) := by
  have hx : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hy : ‖y‖ ≤ Real.sqrt (1 + ‖y‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hm := mul_le_mul hx hy (norm_nonneg y) (Real.sqrt_nonneg (1 + ‖x‖ ^ 2))
  have hn := pow_le_pow_left₀ (norm_nonneg (x + y)) (norm_add_le x y) 2
  have hxs := Real.sq_sqrt (show 0 ≤ 1 + ‖x‖ ^ 2 by positivity)
  have hys := Real.sq_sqrt (show 0 ≤ 1 + ‖y‖ ^ 2 by positivity)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- Exact support-independent Bessel weight splitting, valid for every
natural order (in particular for the tame estimate's `m ≥ 2`). -/
theorem besselWeight_split (m : ℕ) (ξ η : Space) :
    besselWeight m ξ ≤ (2 : ℝ) ^ (m - 1) *
      (besselWeight m η + besselWeight m (ξ - η)) := by
  simp only [besselWeight_eq_sqrt_pow]
  have h := sqrt_bessel_add_le η (ξ - η)
  rw [add_sub_cancel] at h
  exact (pow_le_pow_left₀ (Real.sqrt_nonneg _) h m).trans
    (add_pow_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) m)

/-- Nonnegative weighted Fourier magnitude. -/
def weightedMagnitude (m : ℕ) (φ : SchwartzMap Space ℂ) (ξ : Space) : ℝ :=
  besselWeight m ξ * ‖𝓕 φ ξ‖

theorem weightedMagnitude_nonneg (m : ℕ) (φ : SchwartzMap Space ℂ) (ξ : Space) :
    0 ≤ weightedMagnitude m φ ξ := mul_nonneg (besselWeight_nonneg _ _) (norm_nonneg _)

theorem weightedMagnitude_ae (m : ℕ) (φ : SchwartzMap Space ℂ) :
    (fun ξ => ‖NSFormalization.Paper3.weightedFourierLp m φ ξ‖) =ᵐ[volume]
      weightedMagnitude m φ := by
  filter_upwards [NSFormalization.Paper3.weightedFourierLp_ae m φ] with ξ hξ
  rw [hξ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rfl

theorem weightedMagnitude_memLp (m : ℕ) (φ : SchwartzMap Space ℂ) :
    MemLp (weightedMagnitude m φ) 2 volume :=
  (memLp_congr_ae (weightedMagnitude_ae m φ)).mp
    (Lp.memLp (NSFormalization.Paper3.weightedFourierLp m φ)).norm

theorem weightedMagnitude_norm (m : ℕ) (φ : SchwartzMap Space ℂ) :
    (eLpNorm (weightedMagnitude m φ) 2 volume).toReal =
      ‖NSFormalization.Paper3.weightedFourierLp m φ‖ := by
  rw [← eLpNorm_congr_ae (weightedMagnitude_ae m φ), eLpNorm_norm, Lp.norm_def]

/-- Weight splitting under the actual convolution integral. The two local
integrability hypotheses will be supplied almost everywhere by Young. -/
theorem weighted_product_pointwise_bound (m : ℕ) (φ ψ : SchwartzMap Space ℂ) (ξ : Space)
    (h₁ : Integrable (fun η => weightedMagnitude m φ η * ‖𝓕 ψ (ξ - η)‖) volume)
    (h₂ : Integrable (fun η => ‖𝓕 φ η‖ * weightedMagnitude m ψ (ξ - η)) volume) :
    weightedMagnitude m (schwartzProduct φ ψ) ξ ≤
      (2 : ℝ) ^ (m - 1) *
        ((∫ η : Space, weightedMagnitude m φ η * ‖𝓕 ψ (ξ - η)‖) +
          ∫ η : Space, ‖𝓕 φ η‖ * weightedMagnitude m ψ (ξ - η)) := by
  unfold weightedMagnitude
  rw [fourier_schwartzProduct_apply]
  calc
    _ ≤ besselWeight m ξ * ∫ η : Space, ‖𝓕 φ η * 𝓕 ψ (ξ - η)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (besselWeight_nonneg _ _)
    _ = ∫ η : Space, besselWeight m ξ * ‖𝓕 φ η * 𝓕 ψ (ξ - η)‖ :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ η : Space, (2 : ℝ) ^ (m - 1) *
        (weightedMagnitude m φ η * ‖𝓕 ψ (ξ - η)‖ +
          ‖𝓕 φ η‖ * weightedMagnitude m ψ (ξ - η)) := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall (fun η => mul_nonneg (besselWeight_nonneg _ _) (norm_nonneg _)))
        ((h₁.add h₂).const_mul _)
      filter_upwards with η
      have H := mul_le_mul_of_nonneg_right (besselWeight_split m ξ η)
        (mul_nonneg (norm_nonneg (𝓕 φ η)) (norm_nonneg (𝓕 ψ (ξ - η))))
      simp only [norm_mul, weightedMagnitude, Pi.add_apply]
      nlinarith [H]
    _ = _ := by
      rw [integral_const_mul, integral_add h₁ h₂]
      rfl

/-- Scalar L2 domination and the triangle inequality with finite norms. -/
theorem norm_two_le_scaled_add {f g h : Space → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hdom : ∀ᵐ ξ ∂volume, ‖f ξ‖ ≤ C * (g ξ + h ξ)) :
    (eLpNorm f 2 volume).toReal ≤ C *
      ((eLpNorm g 2 volume).toReal + (eLpNorm h 2 volume).toReal) := by
  have hd : eLpNorm f 2 volume ≤ eLpNorm (C • (g + h)) 2 volume :=
    eLpNorm_mono_ae_real hdom
  have H := ENNReal.toReal_mono ((hg.add hh).const_smul C).2.ne hd
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm,
    Real.norm_eq_abs, abs_of_nonneg hC] at H
  have Hs := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hg.2.ne, hh.2.ne⟩)
    (eLpNorm_add_le hg.1 hh.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  rw [ENNReal.toReal_add hg.2.ne hh.2.ne] at Hs
  exact H.trans (mul_le_mul_of_nonneg_left Hs hC)

/-- The actual Schwartz H2/Hm tame product estimate in cycles-frequency
Bessel norms. The constant depends only on the natural order, not support. -/
theorem schwartz_tame_product (m : ℕ) (φ ψ : SchwartzMap Space ℂ) :
    ‖NSFormalization.Paper3.weightedFourierLp m (schwartzProduct φ ψ)‖ ≤
      ((2 : ℝ) ^ (m - 1) * BesselH2Fourier.besselConstant) *
        (‖NSFormalization.Paper3.weightedFourierLp 2 ψ‖ *
            ‖NSFormalization.Paper3.weightedFourierLp m φ‖ +
          ‖NSFormalization.Paper3.weightedFourierLp 2 φ‖ *
            ‖NSFormalization.Paper3.weightedFourierLp m ψ‖) := by
  let A := NavierStokes.R3ConvolutionYoung.scalarConvolution
    (fun ξ => ‖𝓕 ψ ξ‖) (weightedMagnitude m φ)
  let B := NavierStokes.R3ConvolutionYoung.scalarConvolution
    (fun ξ => ‖𝓕 φ ξ‖) (weightedMagnitude m ψ)
  have HA := YoungConvolution.integrable_convolution_one_two
    (𝓕 ψ).integrable.norm (weightedMagnitude_memLp m φ)
  have HB := YoungConvolution.integrable_convolution_one_two
    (𝓕 φ).integrable.norm (weightedMagnitude_memLp m ψ)
  have hdom : ∀ᵐ ξ ∂volume, ‖weightedMagnitude m (schwartzProduct φ ψ) ξ‖ ≤
      (2 : ℝ) ^ (m - 1) * (A ξ + B ξ) := by
    filter_upwards [HA.1, HB.1] with ξ hA hB
    have hA' : Integrable (fun η => weightedMagnitude m φ η * ‖𝓕 ψ (ξ - η)‖) volume := by
      simpa only [sub_sub_cancel, mul_comm] using hA.comp_sub_left ξ
    have H := weighted_product_pointwise_bound m φ ψ ξ hA' hB
    rw [Real.norm_of_nonneg (weightedMagnitude_nonneg _ _ _)]
    change weightedMagnitude m (schwartzProduct φ ψ) ξ ≤ (2 : ℝ) ^ (m - 1) *
      (NavierStokes.R3ConvolutionYoung.scalarConvolution (fun ξ => ‖𝓕 ψ ξ‖)
        (weightedMagnitude m φ) ξ + B ξ)
    rw [YoungConvolution.scalarConvolution_comm (fun ξ => ‖𝓕 ψ ξ‖) (weightedMagnitude m φ)]
    exact H
  have H := norm_two_le_scaled_add (by positivity) HA.2.1 HB.2.1 hdom
  rw [weightedMagnitude_norm] at H
  have hA_bound : (eLpNorm A 2 volume).toReal ≤
      BesselH2Fourier.besselConstant * ‖NSFormalization.Paper3.weightedFourierLp 2 ψ‖ *
        ‖NSFormalization.Paper3.weightedFourierLp m φ‖ := by
    have H₁ := HA.2.2
    simp only [norm_norm, weightedMagnitude_norm] at H₁
    exact H₁.trans (mul_le_mul_of_nonneg_right
      (BesselH2Fourier.schwartz_fourier_integral_bound ψ) (norm_nonneg _))
  have hB_bound : (eLpNorm B 2 volume).toReal ≤
      BesselH2Fourier.besselConstant * ‖NSFormalization.Paper3.weightedFourierLp 2 φ‖ *
        ‖NSFormalization.Paper3.weightedFourierLp m ψ‖ := by
    have H₂ := HB.2.2
    simp only [norm_norm, weightedMagnitude_norm] at H₂
    exact H₂.trans (mul_le_mul_of_nonneg_right
      (BesselH2Fourier.schwartz_fourier_integral_bound φ) (norm_nonneg _))
  calc
    _ ≤ (2 : ℝ) ^ (m - 1) * ((eLpNorm A 2 volume).toReal +
        (eLpNorm B 2 volume).toReal) := H
    _ ≤ (2 : ℝ) ^ (m - 1) *
        (BesselH2Fourier.besselConstant * ‖NSFormalization.Paper3.weightedFourierLp 2 ψ‖ *
          ‖NSFormalization.Paper3.weightedFourierLp m φ‖ +
        BesselH2Fourier.besselConstant * ‖NSFormalization.Paper3.weightedFourierLp 2 φ‖ *
          ‖NSFormalization.Paper3.weightedFourierLp m ψ‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hA_bound hB_bound) (by positivity)
    _ = _ := by ring

end NSFormalization.Source.FourierTameProduct
