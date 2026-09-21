import NSFormalization.Paper3.SobolevOrderLowering
import NSFormalization.Source.FourierConvention
import NSFormalization.Source.RealSobolev
import NSFormalization.Paper3.RealPositiveDensity

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Source
open scoped ENNReal SchwartzMap ComplexConjugate

/-- Angular Bessel weighting expressed in cycles-frequency coordinates. -/
def angularWeightSymbol (s : ℝ) (ξ : Space) : ℂ :=
  sobolevBesselWeight s (frequencyUnit • ξ) * sobolevBesselWeight (-s) ξ

private theorem bessel_cancel (s : ℝ) (ξ : Space) :
    sobolevBesselWeight s ξ * sobolevBesselWeight (-s) ξ = 1 := by
  have H := congrFun (sobolevBesselWeight_mul s (-s)) ξ
  simpa [sobolevBesselWeight] using H

theorem angularWeightSymbol_inverse (s : ℝ) (ξ : Space) :
    angularWeightSymbol s ξ * angularWeightSymbol (-s) ξ = 1 := by
  unfold angularWeightSymbol
  rw [neg_neg]
  calc
    _ = (sobolevBesselWeight s (frequencyUnit • ξ) * sobolevBesselWeight (-s) (frequencyUnit • ξ)) *
        (sobolevBesselWeight (-s) ξ * sobolevBesselWeight s ξ) := by ring
    _ = _ := by rw [bessel_cancel, mul_comm (sobolevBesselWeight (-s) ξ), bessel_cancel]; simp

theorem angularWeightSymbol_temperate (s : ℝ) : (angularWeightSymbol s).HasTemperateGrowth := by
  have hW := sobolevBesselWeight_temperate s
  have hV := sobolevBesselWeight_temperate (-s)
  unfold angularWeightSymbol
  exact (hW.comp ((frequencyUnit • ContinuousLinearMap.id ℝ Space).hasTemperateGrowth)).mul hV

theorem angularWeightSymbol_norm_le (s : ℝ) (ξ : Space) :
    ‖angularWeightSymbol s ξ‖ ≤ frequencyUnit ^ |s| := by
  have H := (frequency_weight_equivalence (s := s / 2) (r := ‖ξ‖) frequencyUnit_ge_one).1
  have he : 2 * |s / 2| = |s| := by rw [abs_div]; norm_num; ring
  rw [he] at H
  have hcancel : (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) = 1 := by
    rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero]
  have hn : ‖angularWeightSymbol s ξ‖ =
      (1 + frequencyUnit ^ 2 * ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) := by
    simp only [angularWeightSymbol, sobolevBesselWeight, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + frequencyUnit ^ 2 * ‖ξ‖ ^ 2) _),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2) _)]
  rw [hn]
  exact (mul_le_mul_of_nonneg_right H (by positivity)).trans_eq (by rw [mul_assoc, hcancel, mul_one])

theorem angularWeightSymbol_memLp (s : ℝ) :
    MemLp (angularWeightSymbol s) ⊤ (volume : Measure Space) :=
  memLp_top_of_bound (angularWeightSymbol_temperate s).1.continuous.aestronglyMeasurable
    (frequencyUnit ^ |s|) (Filter.Eventually.of_forall (angularWeightSymbol_norm_le s))

/-- Existing Holder multiplication with the bounded angular weight ratio. -/
def angularWeightMap (s : ℝ) : SobolevHilbert s →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure Space) ⊤ 2 2
    ((angularWeightSymbol_memLp s).toLp _)

theorem angularWeightMap_coeFn (s : ℝ) (h : SobolevHilbert s) :
    (angularWeightMap s h : Space → ℂ) =ᵐ[volume] fun ξ => angularWeightSymbol s ξ * h ξ := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((angularWeightSymbol_memLp s).toLp _) h,
    (angularWeightSymbol_memLp s).coeFn_toLp] with ξ hξ gξ
  simpa [angularWeightMap, gξ] using hξ

theorem angularWeightMap_norm_le (s : ℝ) (h : SobolevHilbert s) :
    ‖angularWeightMap s h‖ ≤ frequencyUnit ^ |s| * ‖h‖ := by
  have hg : ‖(angularWeightSymbol_memLp s).toLp _‖ ≤ frequencyUnit ^ |s| := by
    rw [Lp.norm_toLp]
    have he := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure Space))
      (Filter.Eventually.of_forall (angularWeightSymbol_norm_le s))
    simpa only [eLpNorm_exponent_top, ENNReal.toReal_ofReal (Real.rpow_nonneg frequencyUnit_pos.le _)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  change ‖(ContinuousLinearMap.mul ℂ ℂ).holder 2 _ h‖ ≤ _
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖(angularWeightSymbol_memLp s).toLp _‖ * ‖h‖ :=
      (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le _ _
    _ ≤ 1 * (frequencyUnit ^ |s|) * ‖h‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul (ContinuousLinearMap.opNorm_mul_le ℂ ℂ) hg (norm_nonneg _) (by norm_num)) (norm_nonneg _)
    _ = _ := by ring

theorem angularWeightMap_inverse (s : ℝ) (h : SobolevHilbert s) :
    angularWeightMap (-s) (angularWeightMap s h) = h := by
  apply Lp.ext
  filter_upwards [angularWeightMap_coeFn (-s) (angularWeightMap s h),
    angularWeightMap_coeFn s h] with ξ h₁ h₂
  rw [h₁, h₂, ← mul_assoc, mul_comm (angularWeightSymbol (-s) ξ), angularWeightSymbol_inverse, one_mul]

/-- A complete angular-weight coordinate equivalence; its inverse uses the
negative symbol on the same L2 space, not a different physical order. -/
def angularWeightEquiv (s : ℝ) : SobolevHilbert s ≃L[ℂ] Lp ℂ 2 (volume : Measure Space) where
  toLinearEquiv :=
    { (angularWeightMap s).toLinearMap with
      invFun := angularWeightMap (-s)
      left_inv := angularWeightMap_inverse s
      right_inv := by
        intro k
        apply Lp.ext
        filter_upwards [angularWeightMap_coeFn s (angularWeightMap (-s) k),
          angularWeightMap_coeFn (-s) k] with ξ h₁ h₂
        change angularWeightMap s (angularWeightMap (-s) k) ξ = k ξ
        rw [h₁, h₂, ← mul_assoc, angularWeightSymbol_inverse, one_mul] }
  continuous_toFun := (angularWeightMap s).continuous
  continuous_invFun := (angularWeightMap (-s)).continuous

theorem angularWeightEquiv_norm_le (s : ℝ) (h : SobolevHilbert s) :
    ‖angularWeightEquiv s h‖ ≤ frequencyUnit ^ |s| * ‖h‖ := angularWeightMap_norm_le s h

theorem angularWeightEquiv_symm_norm_le (s : ℝ) (k : Lp ℂ 2 (volume : Measure Space)) :
    ‖(angularWeightEquiv s).symm k‖ ≤ frequencyUnit ^ |s| * ‖k‖ := by
  change ‖angularWeightMap (-s) k‖ ≤ _
  simpa only [abs_neg] using angularWeightMap_norm_le (-s) k

theorem angularWeightMap_toDistribution (s : ℝ) (h : SobolevHilbert s) :
    (angularWeightMap s h : 𝓢'(Space, ℂ)) =
      TemperedDistribution.smulLeftCLM ℂ (angularWeightSymbol s) (h : 𝓢'(Space, ℂ)) := by
  have he : angularWeightMap s h = ((angularWeightSymbol_memLp s).toLp _ • h : Lp ℂ 2 volume) := by
    apply Lp.ext
    filter_upwards [angularWeightMap_coeFn s h,
      Lp.coeFn_lpSMul (r := 2) ((angularWeightSymbol_memLp s).toLp _) h,
      (angularWeightSymbol_memLp s).coeFn_toLp] with ξ hξ kξ gξ
    simp [hξ, kξ, gξ]
  rw [he]
  exact Lp.toTemperedDistribution_smul_eq (angularWeightSymbol_temperate s)
    (angularWeightSymbol_memLp s) h

/-- Physical realization of angular-weight coordinates. -/
def angularCoordinateRealization (s : ℝ) : Lp ℂ 2 (volume : Measure Space) →L[ℂ] 𝓢'(Space, ℂ) :=
  (sobolevRealization s).comp (angularWeightEquiv s).symm.toContinuousLinearMap

@[simp] theorem angularCoordinateRealization_equiv (s : ℝ) (h : SobolevHilbert s) :
    angularCoordinateRealization s (angularWeightEquiv s h) = sobolevRealization s h := by
  simp [angularCoordinateRealization]

/-- The coordinate model has the actual angular Bessel weight in cycles
coordinates, on every complete datum. -/
theorem fourier_angularCoordinateRealization (s : ℝ) (k : Lp ℂ 2 (volume : Measure Space)) :
    𝓕 (angularCoordinateRealization s k) =
      TemperedDistribution.smulLeftCLM ℂ (fun ξ => sobolevBesselWeight (-s) (frequencyUnit • ξ))
        (k : 𝓢'(Space, ℂ)) := by
  change 𝓕 (𝓕⁻ (sobolevWeightMultiplier (-s) (angularWeightMap (-s) k : 𝓢'(Space, ℂ)))) = _
  rw [fourier_fourierInv_eq, angularWeightMap_toDistribution]
  change TemperedDistribution.smulLeftCLM ℂ (sobolevBesselWeight (-s))
    (TemperedDistribution.smulLeftCLM ℂ (angularWeightSymbol (-s)) _) = _
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (angularWeightSymbol_temperate (-s)) (sobolevBesselWeight_temperate (-s))]
  apply congrArg (fun g => TemperedDistribution.smulLeftCLM ℂ g (k : 𝓢'(Space, ℂ)))
  funext ξ
  change angularWeightSymbol (-s) ξ * sobolevBesselWeight (-s) ξ = _
  unfold angularWeightSymbol
  rw [neg_neg, mul_assoc, bessel_cancel, mul_one]

theorem angularCoordinateRealization_injective (s : ℝ) :
    Function.Injective (angularCoordinateRealization s) :=
  (sobolevRealization_injective s).comp (angularWeightEquiv s).symm.injective

theorem range_angularCoordinateRealization (s : ℝ) :
    Set.range (angularCoordinateRealization s) = Set.range (sobolevRealization s) := by
  ext u
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(angularWeightEquiv s).symm k, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨angularWeightEquiv s h, angularCoordinateRealization_equiv s h⟩

/-- Schwartz data in angular-weight coordinates. -/
def angularCoordinateDatum (s : ℝ) : SchwartzMap Space ℂ →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  ((angularWeightEquiv s).toContinuousLinearMap.restrictScalars ℝ).comp (weightedFourierLp s)

theorem angularCoordinateDatum_ae (s : ℝ) (φ : SchwartzMap Space ℂ) :
    (angularCoordinateDatum s φ : Space → ℂ) =ᵐ[volume]
      fun ξ => sobolevBesselWeight s (frequencyUnit • ξ) * 𝓕 φ ξ := by
  filter_upwards [angularWeightMap_coeFn s (weightedFourierLp s φ), weightedFourierLp_ae s φ]
    with ξ hT hF
  change angularWeightMap s (weightedFourierLp s φ) ξ = _
  rw [hT, hF, Complex.real_smul]
  change angularWeightSymbol s ξ * (sobolevBesselWeight s ξ * 𝓕 φ ξ) = _
  unfold angularWeightSymbol
  calc
    _ = sobolevBesselWeight s (frequencyUnit • ξ) *
        (sobolevBesselWeight s ξ * sobolevBesselWeight (-s) ξ) * 𝓕 φ ξ := by ring
    _ = _ := by rw [bessel_cancel]; simp

private theorem scaled_bessel_norm_sq (s : ℝ) (ξ : Space) :
    ‖sobolevBesselWeight s (frequencyUnit • ξ)‖ ^ 2 =
      (1 + frequencyUnit ^ 2 * ‖ξ‖ ^ 2) ^ s := by
  simp only [sobolevBesselWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num only [Nat.cast_ofNat]
  rw [show s / 2 * (2 : ℝ) = s by ring]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem angularCoordinateDatum_norm_sq_ae (s : ℝ) (φ : SchwartzMap Space ℂ) :
    (fun ξ => ‖angularCoordinateDatum s φ ξ‖ ^ 2) =ᵐ[volume]
      fun ξ => (1 + frequencyUnit ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 φ ξ‖ ^ 2 := by
  filter_upwards [angularCoordinateDatum_ae s φ] with ξ hξ
  rw [hξ, norm_mul, mul_pow, scaled_bessel_norm_sq]

/-- Genuine weighted integrability accompanies the norm identification. -/
theorem angularCoordinateDatum_weighted_integrable (s : ℝ) (φ : SchwartzMap Space ℂ) :
    Integrable (fun ξ => (1 + frequencyUnit ^ 2 * ‖ξ‖ ^ 2) ^ s * ‖𝓕 φ ξ‖ ^ 2) volume := by
  have H := (memLp_two_iff_integrable_sq_norm (Lp.memLp (angularCoordinateDatum s φ)).1).mp
    (Lp.memLp (angularCoordinateDatum s φ))
  exact H.congr (angularCoordinateDatum_norm_sq_ae s φ)

/-- Exact manuscript angular norm on the Schwartz core. -/
theorem norm_angularCoordinateDatum (s : ℝ) (φ : SchwartzMap Space ℂ) :
    ‖angularCoordinateDatum s φ‖ = angularSobolevNorm s (φ : Space → ℂ) := by
  rw [Lp.norm_def, (Lp.memLp (angularCoordinateDatum s φ)).eLpNorm_eq_integral_rpow_norm
    (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.sqrt_eq_rpow]
  unfold angularSobolevNorm
  rw [angularSobolevSq_eq_frequency_weight]
  apply congrArg Real.sqrt
  exact integral_congr_ae (angularCoordinateDatum_norm_sq_ae s φ)

@[simp] theorem angularCoordinateRealization_datum (s : ℝ) (φ : SchwartzMap Space ℂ) :
    angularCoordinateRealization s (angularCoordinateDatum s φ) = (φ : 𝓢'(Space, ℂ)) := by
  change angularCoordinateRealization s (angularWeightEquiv s (weightedFourierLp s φ)) = _
  rw [angularCoordinateRealization_equiv, sobolevRealization_weightedFourierLp]

theorem denseRange_angularCoordinateDatum (s : ℝ) : DenseRange (angularCoordinateDatum s) :=
  (angularWeightEquiv s).surjective.denseRange.comp (denseRange_weightedFourierLp s)
    (angularWeightEquiv s).continuous

private theorem angularWeightSymbol_neg (s : ℝ) (ξ : Space) :
    angularWeightSymbol s (-ξ) = angularWeightSymbol s ξ := by
  simp [angularWeightSymbol, sobolevBesselWeight]

private theorem angularWeightSymbol_conj (s : ℝ) (ξ : Space) :
    conj (angularWeightSymbol s ξ) = angularWeightSymbol s ξ := by
  simp [angularWeightSymbol, sobolevBesselWeight]

/-- Real-valued even weighting commutes with actual conjugate reflection. -/
theorem angularWeightEquiv_realSymmetry (s : ℝ) (h : SobolevHilbert s) :
    RealSobolev.realSymmetry (angularWeightEquiv s h) =
      angularWeightEquiv s (RealSobolev.realSymmetry h) := by
  apply Lp.ext
  have hr := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (angularWeightMap_coeFn s h)
  filter_upwards [RealSobolev.realSymmetry_ae (angularWeightEquiv s h),
    angularWeightMap_coeFn s (RealSobolev.realSymmetry h), RealSobolev.realSymmetry_ae h, hr]
    with ξ h₁ h₂ h₃ h₄
  change RealSobolev.realSymmetry (angularWeightMap s h) ξ =
    angularWeightMap s (RealSobolev.realSymmetry h) ξ
  change RealSobolev.realSymmetry (angularWeightMap s h) ξ =
    conj (angularWeightMap s h (-ξ)) at h₁
  rw [h₁, h₂, h₃, h₄, map_mul, angularWeightSymbol_neg, angularWeightSymbol_conj]

theorem angularWeightEquiv_mem_realSubspace (s : ℝ) (h : SobolevHilbert s) :
    angularWeightEquiv s h ∈ RealSobolev.realSubspace s ↔ h ∈ RealSobolev.realSubspace s := by
  rw [RealSobolev.mem_realSubspace_iff, RealSobolev.mem_realSubspace_iff,
    angularWeightEquiv_realSymmetry]
  exact (angularWeightEquiv s).injective.eq_iff

/-- Restriction of the same coordinate equivalence to the existing closed
real Sobolev subspace, using Mathlib's submodule restriction. -/
def angularWeightRealEquiv (s : ℝ) :
    RealSobolev.RealSobolevHilbert s ≃L[ℝ] RealSobolev.RealSobolevHilbert s :=
  ((angularWeightEquiv s).restrictScalars ℝ).ofSubmodules
    (RealSobolev.realSubspace s).toSubmodule (RealSobolev.realSubspace s).toSubmodule (by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (angularWeightEquiv_mem_realSubspace s x).mpr hx
      · intro hy
        refine ⟨(angularWeightEquiv s).symm y, ?_, (angularWeightEquiv s).apply_symm_apply y⟩
        apply (angularWeightEquiv_mem_realSubspace s _).mp
        change y ∈ RealSobolev.realSubspace s at hy
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy)

theorem angularWeightRealEquiv_norm_le (s : ℝ) (h : RealSobolev.RealSobolevHilbert s) :
    ‖angularWeightRealEquiv s h‖ ≤ frequencyUnit ^ |s| * ‖h‖ :=
  angularWeightEquiv_norm_le s h

theorem angularWeightRealEquiv_symm_norm_le (s : ℝ) (h : RealSobolev.RealSobolevHilbert s) :
    ‖(angularWeightRealEquiv s).symm h‖ ≤ frequencyUnit ^ |s| * ‖h‖ :=
  angularWeightEquiv_symm_norm_le s h

theorem angularWeightEquiv_coeFn (s : ℝ) (h : SobolevHilbert s) :
    (angularWeightEquiv s h : Space → ℂ) =ᵐ[volume] fun ξ => angularWeightSymbol s ξ * h ξ :=
  angularWeightMap_coeFn s h

@[simp] theorem angularWeightEquiv_symm_apply (s : ℝ) (k : Lp ℂ 2 (volume : Measure Space)) :
    (angularWeightEquiv s).symm k = angularWeightEquiv (-s) k := rfl

theorem angularWeightEquiv_opNorm_le (s : ℝ) :
    ‖(angularWeightEquiv s).toContinuousLinearMap‖ ≤ frequencyUnit ^ |s| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg frequencyUnit_pos.le _)
  exact angularWeightEquiv_norm_le s

theorem angularWeightEquiv_symm_opNorm_le (s : ℝ) :
    ‖(angularWeightEquiv s).symm.toContinuousLinearMap‖ ≤ frequencyUnit ^ |s| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg frequencyUnit_pos.le _)
  exact angularWeightEquiv_symm_norm_le s

end NSFormalization.Paper3
