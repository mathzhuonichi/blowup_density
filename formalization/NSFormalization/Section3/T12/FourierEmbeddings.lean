import NSFormalization.Section3.T12.SpectralGap
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section3.T10.Parseval
import NSFormalization.Section3.T11.MildPressure

/-!
# Fourier-side embeddings for the T12 mean-zero periodic Sobolev calculus

Three fields of `MeanZeroSobolevCalculusAPI`
(`research/T12/probes/api_on_canonical.lean`) are proved here with explicit
constants:

* `boundedRepresentative` — `‖v‖_{L^∞(T³)} ≤ Cinfty ‖v‖_{H²(T³)}` for every
  periodic `L²` field with a finite order-two datum, with
  `Cinfty = (∑_k (1+4π²|k|²)^{-2})^{1/2}` (`linftyConst`).  The route is
  Cauchy–Schwarz on the lattice, `L²`-Fourier inversion through the Hilbert
  basis (the absolutely convergent series is a continuous representative), and
  the `PiLp 2` assembly of the three components.
* `hTwo_le_laplacian` — `‖v‖_{H²} ≤ CHtwo ‖Δv‖_{L²}` for smooth mean-zero
  periodic fields, with `CHtwo = 1 + 1/(4π²)` (`hTwoConst`).  The route is
  coefficientwise: the bounded diagonal reweighting `SpectralGap.reweightDatum`
  applied to the order-zero datum of `Δv`, with the zero mode killed by the
  physical mean-zero hypothesis.
* `lambda_exists` — every smooth periodic field has a smooth periodic physical
  representative of `Λv = (-Δ)^{1/2}v`, built as the Fourier series with
  multiplier `2π|k| = sqrt(4π²|k|²)`.

No named input is assumed and no statement is weakened.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11 (torusScalarSeries)
open scoped ENNReal BigOperators ContDiff ComplexConjugate

/-! ## 0. Elementary facts about the two lattice weights -/

theorem fourierWeight_pos (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  positivity

theorem fourierWeight_eq_one_add_angular (k : PeriodicFrequency) :
    periodicFrequencyWeight k = 1 + periodicAngularFrequencySq k := by
  simp [periodicFrequencyWeight, periodicAngularFrequencySq]

theorem one_le_fourierWeight (k : PeriodicFrequency) : 1 ≤ periodicFrequencyWeight k := by
  rw [fourierWeight_eq_one_add_angular]
  have := angularFrequencySq_nonneg k
  linarith

theorem fourierWeight_neg (k : PeriodicFrequency) :
    periodicFrequencyWeight (-k) = periodicFrequencyWeight k := by
  simp [periodicFrequencyWeight]

theorem angularFrequencySq_neg (k : PeriodicFrequency) :
    periodicAngularFrequencySq (-k) = periodicAngularFrequencySq k := by
  simp [periodicAngularFrequencySq]

/-- Away from the zero mode the angular weight is at least `4π²`. -/
theorem four_pi_sq_le_angularFrequencySq {k : PeriodicFrequency} (hk : k ≠ 0) :
    4 * Real.pi ^ 2 ≤ periodicAngularFrequencySq k := by
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 :=
    mul_pos (by norm_num) (pow_pos Real.pi_pos 2)
  have h := NSFormalization.Section3.T11.mildPressure_one_le_sq_sum hk
  have := mul_le_mul_of_nonneg_left h hpi.le
  simpa only [periodicAngularFrequencySq, mul_one] using this

theorem angularFrequencySq_pos {k : PeriodicFrequency} (hk : k ≠ 0) :
    0 < periodicAngularFrequencySq k :=
  lt_of_lt_of_le (mul_pos (by norm_num) (pow_pos Real.pi_pos 2))
    (four_pi_sq_le_angularFrequencySq hk)

theorem sqrt_angularFrequencySq_le_weight (k : PeriodicFrequency) :
    Real.sqrt (periodicAngularFrequencySq k) ≤ periodicFrequencyWeight k := by
  have hw := fourierWeight_pos k
  have hle : periodicAngularFrequencySq k ≤ periodicFrequencyWeight k ^ 2 := by
    rw [fourierWeight_eq_one_add_angular]
    have := angularFrequencySq_nonneg k
    nlinarith
  calc Real.sqrt (periodicAngularFrequencySq k)
      ≤ Real.sqrt (periodicFrequencyWeight k ^ 2) := Real.sqrt_le_sqrt hle
    _ = periodicFrequencyWeight k := Real.sqrt_sq hw.le

/-- Extended-norm form of `SpectralGap.reweightDatum_norm_le`. -/
theorem reweightDatum_enorm_le' (w : PeriodicFrequency → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (A : PeriodicVectorData) :
    ‖reweightDatum w C hC hw A‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ := by
  calc ‖reweightDatum w C hC hw A‖ₑ = ENNReal.ofReal ‖reweightDatum w C hC hw A‖ :=
        (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (C * ‖A‖) :=
        ENNReal.ofReal_le_ofReal (reweightDatum_norm_le w C hC hw A)
    _ = ENNReal.ofReal C * ENNReal.ofReal ‖A‖ := ENNReal.ofReal_mul hC
    _ = ENNReal.ofReal C * ‖A‖ₑ := by rw [ofReal_norm]

/-! ## 1. Smoothness and periodicity of the registered Laplacian spelling -/

theorem contDiff_laplacian {v : SpatialField} (hs : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (laplacian v) := by
  have hd (j : Fin 3) : ContDiff ℝ ∞ (NSFormalization.Section4.A05.dirDeriv j v) :=
    (hs.fderiv_right (by simp)).clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun x ↦ ∑ j : Fin 3,
    NSFormalization.Section4.A05.dirDeriv j (NSFormalization.Section4.A05.dirDeriv j v) x)
  exact ContDiff.sum fun j _ ↦ (((hd j).fderiv_right (by simp)).clm_apply contDiff_const)

theorem isPeriodicSpatial_laplacian {v : SpatialField} (hp : IsPeriodicSpatial v) :
    IsPeriodicSpatial (laplacian v) := by
  have hup : NavierStokes.PeriodicIntegration.UnitPeriods v := fun x i ↦ hp x i
  intro x j
  show (∑ i : Fin 3, NSFormalization.Section4.A05.dirDeriv i
      (NSFormalization.Section4.A05.dirDeriv i v) (x + coordinateVector j)) =
    ∑ i : Fin 3, NSFormalization.Section4.A05.dirDeriv i
      (NSFormalization.Section4.A05.dirDeriv i v) x
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact NavierStokes.PeriodicUniqueness.spatial_partial_periodic
    (NavierStokes.PeriodicUniqueness.spatial_partial_periodic hup i) i x j

/-! ## 2. `‖v‖_{H²} ≤ (1 + 1/(4π²)) ‖Δv‖_{L²}` on mean-zero smooth periodic fields -/

/-- `03-torus.tex:490-500`: the explicit mean-zero `H²`/Laplacian comparison
constant in the unit-period convention. -/
def hTwoConst : ℝ := 1 + 1 / (4 * Real.pi ^ 2)

theorem hTwoConst_pos : 0 < hTwoConst := by
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := mul_pos (by norm_num) (pow_pos Real.pi_pos 2)
  unfold hTwoConst
  positivity

/-- The Fourier multiplier carrying the order-zero datum of `Δv` to the
order-two datum of `v`; the zero mode is deleted by the mean-zero hypothesis. -/
def laplacianToWeight (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0 else -(periodicFrequencyWeight k / periodicAngularFrequencySq k)

theorem laplacianToWeight_abs_le (k : PeriodicFrequency) :
    |laplacianToWeight k| ≤ hTwoConst := by
  by_cases hk : k = 0
  · simp [laplacianToWeight, hk, hTwoConst_pos.le]
  · have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := mul_pos (by norm_num) (pow_pos Real.pi_pos 2)
    have ha := angularFrequencySq_pos hk
    have h4 := four_pi_sq_le_angularFrequencySq hk
    have hw := fourierWeight_pos k
    simp only [laplacianToWeight, hk, ↓reduceIte, abs_neg,
      abs_of_nonneg (div_nonneg hw.le ha.le)]
    rw [div_le_iff₀ ha, fourierWeight_eq_one_add_angular]
    have hone : 1 ≤ periodicAngularFrequencySq k / (4 * Real.pi ^ 2) :=
      (le_div_iff₀ hpi).2 (by linarith)
    have hexp : hTwoConst * periodicAngularFrequencySq k =
        periodicAngularFrequencySq k + periodicAngularFrequencySq k / (4 * Real.pi ^ 2) := by
      unfold hTwoConst
      field_simp
    rw [hexp]
    linarith

theorem laplacianToWeight_neg (k : PeriodicFrequency) :
    laplacianToWeight (-k) = laplacianToWeight k := by
  simp only [laplacianToWeight, neg_eq_zero, fourierWeight_neg, angularFrequencySq_neg]

/-- `03-torus.tex:490-500`, the `hTwo_le_laplacian` field of
`MeanZeroSobolevCalculusAPI` with `CHtwo := hTwoConst`. -/
theorem hTwo_le_laplacian :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicSobolevENorm 2 v ≤
        ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) := by
  intro v hv hm
  obtain ⟨hs, hp⟩ := hv
  have hlapS : ContDiff ℝ ∞ (laplacian v) := contDiff_laplacian hs
  have hlapP : IsPeriodicSpatial (laplacian v) := isPeriodicSpatial_laplacian hp
  obtain ⟨B, hB⟩ := smooth_periodic_datum 0 hlapS hlapP
  have hvint : Integrable (torusLift v) periodicTorusMeasure :=
    (memLp_torusLift_vector hs.continuous 1).integrable le_rfl
  have hBk : ∀ (i : Fin 3) (k : PeriodicFrequency), B.1 i k =
      (-(periodicAngularFrequencySq k : ℂ)) *
        periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k := by
    intro i k
    have h := hB.2.2 i k
    rw [periodicFourierCoeff_vector_laplacian hp hs i k] at h
    simpa using h
  let A : PeriodicSobolev (2 : ℝ) :=
    ⟨reweightDatum laplacianToWeight hTwoConst hTwoConst_pos.le laplacianToWeight_abs_le B.1,
      reweightDatum_real laplacianToWeight hTwoConst hTwoConst_pos.le laplacianToWeight_abs_le
        laplacianToWeight_neg B⟩
  have hA : IsPeriodicDatum (2 : ℝ) v A := by
    refine ⟨hp, hvint, ?_⟩
    intro i k
    change reweightDatum laplacianToWeight hTwoConst hTwoConst_pos.le
      laplacianToWeight_abs_le B.1 i k = _
    rw [reweightDatum_apply, hBk i k, show ((2 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
    by_cases hk : k = 0
    · subst k
      have hzero : periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) 0 = 0 := by
        rw [periodicFourierCoeff_zero_eq_mean_component hvint i, hm]
        simp
      simp [laplacianToWeight, hzero]
    · have ha := angularFrequencySq_pos hk
      have hane : (periodicAngularFrequencySq k : ℂ) ≠ 0 := by
        simpa using ha.ne'
      simp only [laplacianToWeight, hk, ↓reduceIte]
      change ((-(periodicFrequencyWeight k / periodicAngularFrequencySq k) : ℝ) : ℂ) *
          ((-(periodicAngularFrequencySq k : ℂ)) *
            periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k) =
        ((periodicFrequencyWeight k : ℝ) : ℂ) *
          periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k
      rw [← mul_assoc]
      congr 1
      push_cast
      field_simp
  calc periodicSobolevENorm 2 v ≤ ‖A.1‖ₑ := iInf_le_of_le ⟨A, hA⟩ le_rfl
    _ ≤ ENNReal.ofReal hTwoConst * ‖B.1‖ₑ :=
        reweightDatum_enorm_le' laplacianToWeight hTwoConst hTwoConst_pos.le
          laplacianToWeight_abs_le B.1
    _ = ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) := by
        rw [show ‖B.1‖ₑ = ‖B‖ₑ from rfl,
          parseval_forward (laplacian v) B hB (memLp_torusLift_vector hlapS.continuous 2)]
        rfl

/-! ## 3. Existence of the physical `Λv` representative -/

/-- `appendix-b-embeddings.tex:8-9,97`: the coefficient family of `Λv = (-Δ)^{1/2}v`,
fixed by the unit-torus multiplier `2π|k| = sqrt(4π²|k|²)`. -/
def lambdaCoeff (v : SpatialField) (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (Real.sqrt (periodicAngularFrequencySq k) : ℂ) *
    periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k

/-- The chosen smooth periodic physical representative of `Λv`. -/
def lambdaField (v : SpatialField) : SpatialField := fun x ↦
  NavierStokes.PeriodicIntegration.toSpace
    (fun i ↦ (torusScalarSeries (lambdaCoeff v i) x).re)

theorem lambdaCoeff_neg (v : SpatialField) (i : Fin 3) (k : PeriodicFrequency) :
    lambdaCoeff v i (-k) = star (lambdaCoeff v i k) := by
  unfold lambdaCoeff
  rw [angularFrequencySq_neg, periodicFourierCoeff_real_neg (fun x ↦ v x i) k]
  simp

theorem summable_lambdaCoeff_weighted {v : SpatialField} (hs : ContDiff ℝ ∞ v)
    (hp : IsPeriodicSpatial v) (i : Fin 3) (N : ℕ) :
    Summable (fun k ↦ periodicFrequencyWeight k ^ N * ‖lambdaCoeff v i k‖) := by
  have hcs : ContDiff ℝ ∞ (fun x ↦ ((v x i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)
  have hcp : IsPeriodicSpatial (fun x ↦ ((v x i : ℝ) : ℂ)) :=
    fun x l ↦ congrArg (fun y : Space ↦ ((y i : ℝ) : ℂ)) (hp x l)
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (pow_nonneg (fourierWeight_pos k).le N) (norm_nonneg _))
    (fun k ↦ ?_)
    (NSFormalization.Section3.T11.summable_weight_pow_mul_coeff hcp hcs (N + 1))
  have hnorm : ‖lambdaCoeff v i k‖ = Real.sqrt (periodicAngularFrequencySq k) *
      ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ := by
    unfold lambdaCoeff
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  have hfac : (0 : ℝ) ≤ periodicFrequencyWeight k ^ N *
      ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ :=
    mul_nonneg (pow_nonneg (fourierWeight_pos k).le N) (norm_nonneg _)
  rw [hnorm, pow_succ]
  calc periodicFrequencyWeight k ^ N * (Real.sqrt (periodicAngularFrequencySq k) *
          ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖)
      = (periodicFrequencyWeight k ^ N *
          ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖) *
          Real.sqrt (periodicAngularFrequencySq k) := by ring
    _ ≤ (periodicFrequencyWeight k ^ N *
          ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖) *
          periodicFrequencyWeight k :=
        mul_le_mul_of_nonneg_left (sqrt_angularFrequencySq_le_weight k) hfac
    _ = periodicFrequencyWeight k ^ N * periodicFrequencyWeight k *
          ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ := by ring

theorem summable_lambdaCoeff {v : SpatialField} (hs : ContDiff ℝ ∞ v)
    (hp : IsPeriodicSpatial v) (i : Fin 3) :
    Summable (fun k ↦ ‖lambdaCoeff v i k‖) := by
  simpa using summable_lambdaCoeff_weighted hs hp i 0

theorem contDiff_lambdaSeries {v : SpatialField} (hs : ContDiff ℝ ∞ v)
    (hp : IsPeriodicSpatial v) (i : Fin 3) :
    ContDiff ℝ ∞ (torusScalarSeries (lambdaCoeff v i)) :=
  NSFormalization.Section3.T11.torusScalarSeries_contDiff
    (summable_lambdaCoeff_weighted hs hp i)

theorem lambdaSeries_ofReal_re (v : SpatialField) (i : Fin 3) (x : Space) :
    (((torusScalarSeries (lambdaCoeff v i) x).re : ℝ) : ℂ) =
      torusScalarSeries (lambdaCoeff v i) x :=
  Complex.conj_eq_iff_re.mp
    (NSFormalization.Section3.T11.torusScalarSeries_conj (lambdaCoeff_neg v i) x)

theorem lambdaField_component (v : SpatialField) (i : Fin 3) :
    (fun x ↦ ((lambdaField v x i : ℝ) : ℂ)) = torusScalarSeries (lambdaCoeff v i) :=
  funext fun x ↦ lambdaSeries_ofReal_re v i x

/-- `appendix-b-embeddings.tex:8-9,97`, the `lambda_exists` field of
`MeanZeroSobolevCalculusAPI`. -/
theorem lambda_exists :
    ∀ v : SpatialField, SmoothPeriodicT v →
      ∃ Lv : SpatialField, IsPeriodicLambda v Lv := by
  intro v hv
  obtain ⟨hs, hp⟩ := hv
  refine ⟨lambdaField v, ⟨?_, ?_⟩, ?_⟩
  · have hpi : ContDiff ℝ ∞ (fun x : Space ↦
        (fun i ↦ (torusScalarSeries (lambdaCoeff v i) x).re :
          NavierStokes.PeriodicIntegration.Coords)) :=
      contDiff_pi.mpr fun i ↦ Complex.reCLM.contDiff.comp (contDiff_lambdaSeries hs hp i)
    exact (NavierStokes.PeriodicIntegration.toSpace :
      NavierStokes.PeriodicIntegration.Coords →L[ℝ] Space).contDiff.comp hpi
  · intro x j
    show NavierStokes.PeriodicIntegration.toSpace
        (fun i ↦ (torusScalarSeries (lambdaCoeff v i) (x + coordinateVector j)).re) =
      NavierStokes.PeriodicIntegration.toSpace
        (fun i ↦ (torusScalarSeries (lambdaCoeff v i) x).re)
    congr 1
    funext i
    rw [NSFormalization.Section3.T11.torusScalarSeries_periodic (lambdaCoeff v i) x j]
  · intro i k
    rw [lambdaField_component v i,
      NSFormalization.Section3.T11.torusScalarSeries_coeff (summable_lambdaCoeff hs hp i) k]
    rfl

/-! ## 4. `‖v‖_{L^∞(T³)} ≤ Cinfty ‖v‖_{H²(T³)}` -/

/-- `appendix-a-local-theory.tex:12,44-47`: the explicit `H²(T³) → L^∞(T³)`
constant, the `ℓ²` norm of the inverse Bessel weights. -/
def linftyConst : ℝ :=
  Real.sqrt (∑' k : PeriodicFrequency, (periodicFrequencyWeight k ^ 2)⁻¹)

theorem one_le_inverseWeightSum :
    1 ≤ ∑' k : PeriodicFrequency, (periodicFrequencyWeight k ^ 2)⁻¹ := by
  have hz : (periodicFrequencyWeight (0 : PeriodicFrequency) ^ 2)⁻¹ = 1 := by
    simp [periodicFrequencyWeight]
  have h := summable_inverse_periodicFrequencyWeight.le_tsum (0 : PeriodicFrequency)
    (fun k _ ↦ inv_nonneg.mpr (sq_nonneg _))
  rwa [hz] at h

theorem linftyConst_pos : 0 < linftyConst :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one one_le_inverseWeightSum)

/-! ### The absolutely convergent Fourier series is a continuous representative -/

theorem continuous_torusScalarSeries {c : PeriodicFrequency → ℂ}
    (hc : Summable (fun k ↦ ‖c k‖)) : Continuous (torusScalarSeries c) := by
  show Continuous fun x ↦ ∑' k, c k * NSFormalization.Paper1.periodicCharacter k x
  refine continuous_tsum (u := fun k ↦ ‖c k‖)
    (fun k ↦ continuous_const.mul
      (NSFormalization.Paper1.periodicCharacter_smooth k).continuous) hc (fun k x ↦ ?_)
  rw [norm_mul, NSFormalization.Section3.T11.torusCharacter_norm, mul_one]

theorem norm_torusScalarSeries_le {c : PeriodicFrequency → ℂ}
    (hc : Summable (fun k ↦ ‖c k‖)) (x : Space) :
    ‖torusScalarSeries c x‖ ≤ ∑' k, ‖c k‖ := by
  have hn : ∀ k, ‖c k * NSFormalization.Paper1.periodicCharacter k x‖ = ‖c k‖ := fun k ↦ by
    rw [norm_mul, NSFormalization.Section3.T11.torusCharacter_norm, mul_one]
  have hsum : Summable (fun k ↦ ‖c k * NSFormalization.Paper1.periodicCharacter k x‖) := by
    simpa only [hn] using hc
  show ‖∑' k, c k * NSFormalization.Paper1.periodicCharacter k x‖ ≤ ∑' k, ‖c k‖
  calc ‖∑' k, c k * NSFormalization.Paper1.periodicCharacter k x‖
      ≤ ∑' k, ‖c k * NSFormalization.Paper1.periodicCharacter k x‖ :=
        norm_tsum_le_tsum_norm hsum
    _ = ∑' k, ‖c k‖ := by simp only [hn]

/-- `L²`-Fourier inversion: a periodic `L²` field with absolutely summable
coefficients agrees almost everywhere with its (continuous) Fourier series. -/
theorem ae_eq_torusScalarSeries {f : Space → ℂ}
    (hf : MemLp (torusLift f) 2 periodicTorusMeasure)
    (hc : Summable (fun k ↦ ‖periodicFourierCoeff f k‖)) :
    torusLift f =ᵐ[periodicTorusMeasure]
      torusLift (torusScalarSeries (periodicFourierCoeff f)) := by
  have hg : Continuous (torusScalarSeries (periodicFourierCoeff f)) :=
    continuous_torusScalarSeries hc
  have hgL : MemLp (torusLift (torusScalarSeries (periodicFourierCoeff f))) 2
      periodicTorusMeasure := NSFormalization.Paper1.memLp_torusLift hg 2
  have heq : hf.toLp (torusLift f) =
      hgL.toLp (torusLift (torusScalarSeries (periodicFourierCoeff f))) := by
    apply (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.injective
    ext k
    rw [fourier_repr_toLp f hf k,
      fourier_repr_toLp (torusScalarSeries (periodicFourierCoeff f)) hgL k,
      NSFormalization.Section3.T11.torusScalarSeries_coeff hc k]
  have h1 := hf.coeFn_toLp
  have h2 := hgL.coeFn_toLp
  rw [heq] at h1
  exact h1.symm.trans h2

/-- `appendix-a-local-theory.tex:8-12`, the `boundedRepresentative` field of
`MeanZeroSobolevCalculusAPI` with `Cinfty := linftyConst`. -/
theorem boundedRepresentative :
    ∀ v : SpatialField, MemPeriodicHmVector 2 v →
      periodicLpENorm ⊤ v ≤ ENNReal.ofReal linftyConst * periodicSobolevENorm 2 v := by
  intro v hv
  obtain ⟨hp, hL2, hfin⟩ := hv
  simp only [Nat.cast_ofNat] at hfin
  obtain ⟨A, hA⟩ : ∃ A : PeriodicSobolev (2 : ℝ), IsPeriodicDatum (2 : ℝ) v A := by
    by_contra hnone
    apply hfin
    unfold periodicSobolevENorm
    refine iInf_eq_top.mpr fun A ↦ (hnone ⟨A.1, A.2⟩).elim
  have hAk : ∀ (i : Fin 3) (k : PeriodicFrequency), A.1 i k =
      ((periodicFrequencyWeight k : ℝ) : ℂ) *
        periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k := by
    intro i k
    have h := hA.2.2 i k
    rwa [show ((2 : ℝ) / 2) = 1 by norm_num, Real.rpow_one, Complex.real_smul] at h
  have hNorm : ∀ (i : Fin 3) (k : PeriodicFrequency), ‖A.1 i k‖ =
      periodicFrequencyWeight k * ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ := by
    intro i k
    rw [hAk i k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (fourierWeight_pos k)]
  have hHS : ∀ i : Fin 3, HasSum (fun k ↦ ‖A.1 i k‖ ^ 2) (‖A.1 i‖ ^ 2) := by
    intro i
    have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < ((2 : ℝ≥0∞).toReal)) (A.1 i)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hE : ∀ i : Fin 3, HasSum (fun k ↦ periodicFrequencyWeight k ^ 2 *
      ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ ^ 2) (‖A.1 i‖ ^ 2) := by
    intro i
    have hrw : ∀ k : PeriodicFrequency, periodicFrequencyWeight k ^ 2 *
        ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ ^ 2 = ‖A.1 i k‖ ^ 2 := by
      intro k
      rw [hNorm i k]
      ring
    simpa only [hrw] using hHS i
  have hSummable : ∀ i : Fin 3,
      Summable (fun k ↦ ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖) := by
    intro i
    refine Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_)
      ((summable_inverse_periodicFrequencyWeight.add (hHS i).summable).mul_left (1 / 2))
    have hw := fourierWeight_pos k
    have h1 : ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ =
        (periodicFrequencyWeight k)⁻¹ * ‖A.1 i k‖ := by
      rw [hNorm i k, ← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]
    rw [h1, show (periodicFrequencyWeight k ^ 2)⁻¹ = ((periodicFrequencyWeight k)⁻¹) ^ 2 from
      (inv_pow _ _).symm]
    nlinarith [sq_nonneg ((periodicFrequencyWeight k)⁻¹ - ‖A.1 i k‖)]
  have hL1 : ∀ i : Fin 3,
      (∑' k, ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖) ≤
        linftyConst * ‖A.1 i‖ := by
    intro i
    have h := tsum_norm_periodicFourierCoeff_le (f := fun x ↦ ((v x i : ℝ) : ℂ))
      (hE i).summable
    rwa [(hE i).tsum_eq, Real.sqrt_sq (norm_nonneg _)] at h
  have hcomp : ∀ i : Fin 3, ∀ᵐ y ∂periodicTorusMeasure,
      ‖torusLift v y i‖ ≤ ∑' k, ‖periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k‖ := by
    intro i
    have hmem := memLp_torusLift_component v hL2 i
    filter_upwards [ae_eq_torusScalarSeries hmem (hSummable i)] with y hy
    rw [show ‖torusLift v y i‖ = ‖torusLift (fun x ↦ ((v x i : ℝ) : ℂ)) y‖ from
      (Complex.norm_real _).symm, hy]
    exact norm_torusScalarSeries_le (hSummable i) _
  have hae : ∀ᵐ y ∂periodicTorusMeasure, ‖torusLift v y‖ ≤ linftyConst * ‖A.1‖ := by
    filter_upwards [ae_all_iff.mpr hcomp] with y hy
    have hb : 0 ≤ linftyConst * ‖A.1‖ := mul_nonneg linftyConst_pos.le (norm_nonneg _)
    have hsq : ‖torusLift v y‖ ^ 2 ≤ (linftyConst * ‖A.1‖) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      calc ∑ i : Fin 3, ‖torusLift v y i‖ ^ 2
          ≤ ∑ i : Fin 3, (linftyConst * ‖A.1 i‖) ^ 2 := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact pow_le_pow_left₀ (norm_nonneg _) ((hy i).trans (hL1 i)) 2
        _ = linftyConst ^ 2 * ∑ i : Fin 3, ‖A.1 i‖ ^ 2 := by
            simp only [mul_pow]
            rw [← Finset.mul_sum]
        _ = (linftyConst * ‖A.1‖) ^ 2 := by
            rw [mul_pow, PiLp.norm_sq_eq_of_L2]
    have hroot := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb] at hroot
  have hfinal : periodicLpENorm ⊤ v ≤ ENNReal.ofReal (linftyConst * ‖A.1‖) := by
    show eLpNorm (torusLift v) ⊤ periodicTorusMeasure ≤ _
    rw [eLpNorm_exponent_top]
    show essSup (fun y ↦ ‖torusLift v y‖ₑ) periodicTorusMeasure ≤ _
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hae] with y hy
    calc ‖torusLift v y‖ₑ = ENNReal.ofReal ‖torusLift v y‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (linftyConst * ‖A.1‖) := ENNReal.ofReal_le_ofReal hy
  calc periodicLpENorm ⊤ v ≤ ENNReal.ofReal (linftyConst * ‖A.1‖) := hfinal
    _ = ENNReal.ofReal linftyConst * ‖A.1‖ₑ := by
        rw [ENNReal.ofReal_mul linftyConst_pos.le, ofReal_norm]
    _ = ENNReal.ofReal linftyConst * periodicSobolevENorm 2 v := by
        rw [periodicSobolevENorm_eq hA]
        rfl

end NSFormalization.Section3.T12
