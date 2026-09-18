import NSFormalization.Section3.T12.CriticalL3
import NSFormalization.Section3.T12.FourierEmbeddings
import NSFormalization.Section3.T10.ForcePaths

/-!
# T12 U6: the order-`3/2` sum embedding `gradientLambdaCriticalL3`

For a smooth periodic mean-zero field `v` of order `3/2` and a physical
representative `Lv` of `Λv`, the two critical `L³(T³)` norms of the first-order
quantities are controlled by the homogeneous `Ḣ^{3/2}(T³)` norm
(`appendix-a-local-theory.tex:22-26`, `appendix-b-embeddings.tex:26-31`;
`research/T12/T12_SPLIT.md` U6).

## Route (`research/T12/T12_SPLIT.md` U6)

Both `∂_j v` (each column of `gradientTensor v`) and `Lv` are smooth periodic and
mean-zero, so U4's `velocityCriticalL3_smooth` applies to each of them at order
`1/2`.  The two Fourier order-shift comparisons

* `periodicHomogeneousENorm (1/2) (∂_j v) ≤ periodicHomogeneousENorm (3/2) v`
  (multiplier `2πi k_j / (2π|k|)`, of modulus `|k_j|/|k| ≤ 1`), and
* `periodicHomogeneousENorm (1/2) Lv ≤ periodicHomogeneousENorm (3/2) v`
  (multiplier `2π|k| · |2πk|^{1/2} = |2πk|^{3/2}`, i.e. the *same* datum),

then convert the three order-`1/2` right-hand sides into the single order-`3/2`
norm, and the crude `l² ≤ l¹` bound `‖∇v‖ ≤ ∑_j ‖∂_j v‖` assembles the three
columns into `periodicLpENorm 3 (gradientTensor v)`.

The weight algebra is the identity
`homogeneousDatumWeight (3/2) k = homogeneousDatumWeight (1/2) k · 2π|k|`
(`homogeneousDatumWeight_three_halves`), which is what makes both shifts exact.
`SpectralGap.reweightDatum` only carries *real* multipliers, while the derivative
symbol `2πi k_j` is imaginary, so §1 repeats that construction for a bounded
**complex** multiplier.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.A05 (dirDeriv)
open scoped ContDiff ENNReal BigOperators ComplexConjugate

/-! ## §0  Bounded complex reweighting of the periodic datum carrier -/

/-- Bounded coordinatewise multiplication by a **complex** Fourier multiplier on
the complete periodic vector datum carrier.  This is the complex counterpart of
`SpectralGap.reweightDatum`, needed because the derivative symbol `2πi k_j` is
not real. -/
def cxReweight (w : PeriodicFrequency → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, ‖w k‖ ≤ C) (A : PeriodicVectorData) : PeriodicVectorData :=
  WithLp.toLp 2 (fun i ↦
    ⟨fun k ↦ w k • A i k,
      by
        have hmem : Memℓp (fun k : PeriodicFrequency ↦ (C : ℂ) • A i k) 2 :=
          (lp.memℓp (A i)).const_smul (C : ℂ)
        exact hmem.mono' (fun k ↦ by
          simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
          exact mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _))⟩)

@[simp]
theorem cxReweight_apply (w : PeriodicFrequency → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, ‖w k‖ ≤ C) (A : PeriodicVectorData) (i : Fin 3)
    (k : PeriodicFrequency) :
    cxReweight w C hC hw A i k = w k • A i k := rfl

/-- A bounded complex reweighting has operator norm at most its supplied bound. -/
theorem cxReweight_norm_le (w : PeriodicFrequency → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, ‖w k‖ ≤ C) (A : PeriodicVectorData) :
    ‖cxReweight w C hC hw A‖ ≤ C * ‖A‖ := by
  have hi : ∀ i : Fin 3, ‖cxReweight w C hC hw A i‖ ≤ C * ‖A i‖ := by
    intro i
    have hpoint : ∀ k : PeriodicFrequency,
        ‖cxReweight w C hC hw A i k‖ ≤ ‖((C : ℂ) • A i) k‖ := by
      intro k
      simp only [cxReweight_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _)
    calc
      ‖cxReweight w C hC hw A i‖ ≤ ‖(C : ℂ) • A i‖ :=
        lp.norm_mono (by norm_num) hpoint
      _ = C * ‖A i‖ := by
        rw [norm_smul]
        congr 1
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  have hsq : ‖cxReweight w C hC hw A‖ ^ 2 ≤ (C * ‖A‖) ^ 2 := by
    calc
      ‖cxReweight w C hC hw A‖ ^ 2 = ∑ i : Fin 3, ‖cxReweight w C hC hw A i‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 _ _
      _ ≤ ∑ i : Fin 3, (C * ‖A i‖) ^ 2 := by
        gcongr with i
        exact hi i
      _ = C ^ 2 * ∑ i : Fin 3, ‖A i‖ ^ 2 := by
        simp only [mul_pow]
        rw [Finset.mul_sum]
      _ = (C * ‖A‖) ^ 2 := by
        rw [mul_pow, PiLp.norm_sq_eq_of_L2]
  nlinarith [norm_nonneg (cxReweight w C hC hw A), mul_nonneg hC (norm_nonneg A)]

theorem cxReweight_enorm_le (w : PeriodicFrequency → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, ‖w k‖ ≤ C) (A : PeriodicVectorData) :
    ‖cxReweight w C hC hw A‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ := by
  calc
    ‖cxReweight w C hC hw A‖ₑ = ENNReal.ofReal ‖cxReweight w C hC hw A‖ :=
      (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (C * ‖A‖) :=
      ENNReal.ofReal_le_ofReal (cxReweight_norm_le w C hC hw A)
    _ = ENNReal.ofReal C * ENNReal.ofReal ‖A‖ := ENNReal.ofReal_mul hC
    _ = ENNReal.ofReal C * ‖A‖ₑ := by rw [ofReal_norm]

/-- A conjugate-reflection multiplier preserves the real subspace. -/
theorem cxReweight_real (w : PeriodicFrequency → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, ‖w k‖ ≤ C) (hconj : ∀ k, w (-k) = star (w k))
    (A : realPeriodicSubmodule) :
    cxReweight w C hC hw A.1 ∈ realPeriodicSubmodule := by
  intro i k
  simp only [cxReweight_apply]
  change w (-k) * A.1 i (-k) = star (w k * A.1 i k)
  rw [hconj k, A.2 i k]
  simp

/-! ## §1  The order `1/2` → `3/2` weight algebra -/

/-- `|2πk|^{3/2} = |2πk|^{1/2} · 2π|k|`: the homogeneous multiplier at order
`3/2` factors through the one at order `1/2` and the `Λ` symbol. -/
theorem homogeneousDatumWeight_three_halves (k : PeriodicFrequency) :
    homogeneousDatumWeight (3 / 2) k =
      homogeneousDatumWeight (1 / 2) k * Real.sqrt (periodicAngularFrequencySq k) := by
  by_cases hk : k = 0
  · simp [homogeneousDatumWeight, hk]
  · have hpos := angularFrequencySq_pos hk
    simp only [homogeneousDatumWeight, hk, ↓reduceIte]
    show (periodicAngularFrequencySq k) ^ ((3 : ℝ) / 2 / 2) =
      (periodicAngularFrequencySq k) ^ ((1 : ℝ) / 2 / 2) *
        Real.sqrt (periodicAngularFrequencySq k)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
    norm_num

/-- `2π|k_j| ≤ 2π|k|`, the coordinate-symbol bound. -/
theorem abs_derivSymbol_le_sqrt (j : Fin 3) (k : PeriodicFrequency) :
    |2 * Real.pi * (k j : ℝ)| ≤ Real.sqrt (periodicAngularFrequencySq k) := by
  have hsum : ((k j : ℝ)) ^ 2 ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg ((k i : ℝ))) (Finset.mem_univ j)
  have hpi : (0 : ℝ) ≤ 4 * Real.pi ^ 2 := by positivity
  have hle : (2 * Real.pi * (k j : ℝ)) ^ 2 ≤ periodicAngularFrequencySq k := by
    calc (2 * Real.pi * (k j : ℝ)) ^ 2 = 4 * Real.pi ^ 2 * ((k j : ℝ)) ^ 2 := by ring
      _ ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hpi
      _ = periodicAngularFrequencySq k := rfl
  calc |2 * Real.pi * (k j : ℝ)| = Real.sqrt ((2 * Real.pi * (k j : ℝ)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (periodicAngularFrequencySq k) := Real.sqrt_le_sqrt hle

theorem norm_periodicDerivativeSymbol (j : Fin 3) (k : PeriodicFrequency) :
    ‖periodicDerivativeSymbol j k‖ = |2 * Real.pi * (k j : ℝ)| := by
  have hn : ‖periodicDerivativeSymbol j k‖ = ‖2 * Real.pi * (k j : ℝ)‖ := by
    simp [periodicDerivativeSymbol, norm_mul, mul_assoc]
  rw [hn, Real.norm_eq_abs]

/-- The real half of the order-shift multiplier: `1/(2π|k|)` away from the zero
mode, deleted at the zero mode. -/
def derivShiftReal (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0 else (Real.sqrt (periodicAngularFrequencySq k))⁻¹

theorem derivShiftReal_ne_zero {k : PeriodicFrequency} (hk : k ≠ 0) :
    derivShiftReal k = (Real.sqrt (periodicAngularFrequencySq k))⁻¹ := by
  simp [derivShiftReal, hk]

/-- The Fourier multiplier taking the order-`3/2` datum of `v` to the order-`1/2`
datum of `∂_j v`: `2πi k_j / (2π|k|)`, of modulus `|k_j|/|k| ≤ 1`. -/
def derivShift (j : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (derivShiftReal k : ℂ) * periodicDerivativeSymbol j k

theorem norm_derivShift_le (j : Fin 3) (k : PeriodicFrequency) :
    ‖derivShift j k‖ ≤ 1 := by
  by_cases hk : k = 0
  · simp [derivShift, derivShiftReal, hk]
  · have hpos : 0 < Real.sqrt (periodicAngularFrequencySq k) :=
      Real.sqrt_pos.mpr (angularFrequencySq_pos hk)
    rw [derivShift, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      derivShiftReal_ne_zero hk, abs_of_pos (inv_pos.mpr hpos),
      norm_periodicDerivativeSymbol]
    calc (Real.sqrt (periodicAngularFrequencySq k))⁻¹ * |2 * Real.pi * (k j : ℝ)|
        ≤ (Real.sqrt (periodicAngularFrequencySq k))⁻¹ *
            Real.sqrt (periodicAngularFrequencySq k) :=
          mul_le_mul_of_nonneg_left (abs_derivSymbol_le_sqrt j k) (inv_pos.mpr hpos).le
      _ = 1 := inv_mul_cancel₀ hpos.ne'

theorem derivShift_conj (j : Fin 3) (k : PeriodicFrequency) :
    derivShift j (-k) = star (derivShift j k) := by
  have hr : derivShiftReal (-k) = derivShiftReal k := by
    simp only [derivShiftReal, neg_eq_zero, angularFrequencySq_neg]
  have hs : periodicDerivativeSymbol j (-k) = -periodicDerivativeSymbol j k := by
    simp only [periodicDerivativeSymbol, Pi.neg_apply]
    push_cast
    ring
  have hstar : star (periodicDerivativeSymbol j k) = -periodicDerivativeSymbol j k := by
    simp [periodicDerivativeSymbol]
  have hrr : star ((derivShiftReal k : ℝ) : ℂ) = ((derivShiftReal k : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [derivShift, derivShift, hr, hs, star_mul, hstar, hrr]
  ring

/-! ## §2  The derivative columns: smooth, periodic, mean-zero -/

theorem contDiff_dirDeriv {v : SpatialField} (hs : ContDiff ℝ ∞ v) (j : Fin 3) :
    ContDiff ℝ ∞ (dirDeriv j v) :=
  (hs.fderiv_right (by simp)).clm_apply contDiff_const

theorem isPeriodicSpatial_dirDeriv {v : SpatialField} (hp : IsPeriodicSpatial v)
    (j : Fin 3) : IsPeriodicSpatial (dirDeriv j v) := by
  have hup : NavierStokes.PeriodicIntegration.UnitPeriods v := fun x i ↦ hp x i
  intro x l
  exact NavierStokes.PeriodicUniqueness.spatial_partial_periodic hup j x l

/-- A coordinate derivative of a smooth periodic field has zero torus mean: the
derivative symbol vanishes at the zero mode. -/
theorem isMeanZeroT_dirDeriv {v : SpatialField} (hv : SmoothPeriodicT v) (j : Fin 3) :
    IsMeanZeroT (dirDeriv j v) := by
  obtain ⟨hs, hp⟩ := hv
  have hd : ContDiff ℝ ∞ (dirDeriv j v) := contDiff_dirDeriv hs j
  have hint : Integrable (torusLift (dirDeriv j v)) periodicTorusMeasure :=
    (memLp_torusLift_vector hd.continuous 1).integrable le_rfl
  have hone : ContDiff ℝ 1 v := hs.of_le (by simp)
  have hall : ∀ i, meanT (dirDeriv j v) i = 0 := by
    intro i
    have h0 := periodicFourierCoeff_zero_eq_mean_component hint i
    have hcoef : periodicFourierCoeff (fun x ↦ ((dirDeriv j v x i : ℝ) : ℂ)) 0 =
        periodicDerivativeSymbol j 0 *
          periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) 0 :=
      periodicFourierCoeff_gradientTensor hp hone i j 0
    rw [hcoef] at h0
    have hsym : periodicDerivativeSymbol j (0 : PeriodicFrequency) = 0 := by
      simp [periodicDerivativeSymbol]
    rw [hsym, zero_mul] at h0
    exact_mod_cast h0.symm
  unfold IsMeanZeroT
  ext i
  exact hall i

/-! ## §3  The `Λ` representative: mean-zero -/

theorem isMeanZeroT_lambda {v Lv : SpatialField} (hL : IsPeriodicLambda v Lv) :
    IsMeanZeroT Lv := by
  have hint : Integrable (torusLift Lv) periodicTorusMeasure :=
    (memLp_torusLift_vector hL.1.1.continuous 1).integrable le_rfl
  have hall : ∀ i, meanT Lv i = 0 := by
    intro i
    have h0 := periodicFourierCoeff_zero_eq_mean_component hint i
    have hz : Real.sqrt (periodicAngularFrequencySq (0 : PeriodicFrequency)) = 0 := by
      simp [periodicAngularFrequencySq]
    have h1 : ((meanT Lv i : ℝ) : ℂ) = 0 := by
      rw [← h0, hL.2 i 0, hz]
      simp
    exact Complex.ofReal_eq_zero.mp h1
  unfold IsMeanZeroT
  ext i
  exact hall i

/-! ## §4  The two order-shift comparisons -/

/-- Fourier order shift for a coordinate derivative: the order-`1/2` homogeneous
norm of `∂_j v` is at most the order-`3/2` homogeneous norm of `v`. -/
theorem homogeneousENorm_half_dirDeriv_le (v : SpatialField) (hv : SmoothPeriodicT v)
    (j : Fin 3) :
    periodicHomogeneousENorm (1 / 2) (dirDeriv j v) ≤
      periodicHomogeneousENorm (3 / 2) v := by
  obtain ⟨hs, hp⟩ := hv
  have hone : ContDiff ℝ 1 v := hs.of_le (by simp)
  have hd : ContDiff ℝ ∞ (dirDeriv j v) := contDiff_dirDeriv hs j
  have hdp : IsPeriodicSpatial (dirDeriv j v) := isPeriodicSpatial_dirDeriv hp j
  have hdm : IsMeanZeroT (dirDeriv j v) := isMeanZeroT_dirDeriv ⟨hs, hp⟩ j
  have hdi : Integrable (torusLift (dirDeriv j v)) periodicTorusMeasure :=
    (memLp_torusLift_vector hd.continuous 1).integrable le_rfl
  unfold periodicHomogeneousENorm
  refine le_iInf (fun A ↦ ?_)
  let B : PeriodicSobolev (1 / 2 : ℝ) :=
    ⟨cxReweight (derivShift j) 1 zero_le_one (norm_derivShift_le j) A.1.1,
      cxReweight_real (derivShift j) 1 zero_le_one (norm_derivShift_le j)
        (derivShift_conj j) A.1⟩
  have hB : IsPeriodicHomogeneousDatum (1 / 2) (dirDeriv j v) B := by
    refine ⟨hdp, hdi, hdm, ?_⟩
    intro i k
    have hcoef : periodicFourierCoeff (fun x ↦ ((dirDeriv j v x i : ℝ) : ℂ)) k =
        periodicDerivativeSymbol j k *
          periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k :=
      periodicFourierCoeff_gradientTensor hp hone i j k
    show cxReweight (derivShift j) 1 zero_le_one (norm_derivShift_le j) A.1.1 i k = _
    rw [cxReweight_apply, A.2.2.2.2 i k, hcoef]
    by_cases hk : k = 0
    · subst k
      simp [derivShift, derivShiftReal, homogeneousDatumWeight]
    · have hpos : 0 < Real.sqrt (periodicAngularFrequencySq k) :=
        Real.sqrt_pos.mpr (angularFrequencySq_pos hk)
      have hne : ((Real.sqrt (periodicAngularFrequencySq k) : ℝ) : ℂ) ≠ 0 := by
        simpa using hpos.ne'
      simp only [derivShift, derivShiftReal_ne_zero hk, smul_eq_mul,
        homogeneousDatumWeight_three_halves k]
      push_cast
      field_simp
  calc (⨅ C : {C : PeriodicSobolev (1 / 2 : ℝ) //
        IsPeriodicHomogeneousDatum (1 / 2) (dirDeriv j v) C}, ‖C.1‖ₑ)
      ≤ ‖B.1‖ₑ := iInf_le_of_le ⟨B, hB⟩ le_rfl
    _ ≤ ‖A.1.1‖ₑ := by
        simpa only [ENNReal.ofReal_one, one_mul] using
          cxReweight_enorm_le (derivShift j) 1 zero_le_one (norm_derivShift_le j) A.1.1

/-- Fourier order shift for `Λ`: the order-`1/2` homogeneous datum of `Lv` **is**
the order-`3/2` homogeneous datum of `v`. -/
theorem homogeneousENorm_half_lambda_le (v Lv : SpatialField)
    (hL : IsPeriodicLambda v Lv) :
    periodicHomogeneousENorm (1 / 2) Lv ≤ periodicHomogeneousENorm (3 / 2) v := by
  have hLi : Integrable (torusLift Lv) periodicTorusMeasure :=
    (memLp_torusLift_vector hL.1.1.continuous 1).integrable le_rfl
  have hLm : IsMeanZeroT Lv := isMeanZeroT_lambda hL
  unfold periodicHomogeneousENorm
  refine le_iInf (fun A ↦ ?_)
  have hA : IsPeriodicHomogeneousDatum (1 / 2) Lv A.1 := by
    refine ⟨hL.1.2, hLi, hLm, ?_⟩
    intro i k
    rw [A.2.2.2.2 i k, hL.2 i k, homogeneousDatumWeight_three_halves k]
    push_cast
    ring
  exact iInf_le_of_le ⟨A.1, hA⟩ le_rfl

/-! ## §5  Assembling the three columns of the gradient tensor -/

/-- The torus counterpart of `A05.eLpNorm_le_sum_of_norm_le`. -/
theorem eLpNorm_torus_le_sum_of_norm_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {p : ℝ≥0∞} (hp : 1 ≤ p) {ι : Type*} [Fintype ι]
    {f : PeriodicTorus → E} {g : ι → PeriodicTorus → F}
    (hg : ∀ i, AEStronglyMeasurable (g i) periodicTorusMeasure)
    (h : ∀ y, ‖f y‖ ≤ ∑ i, ‖g i y‖) :
    eLpNorm f p periodicTorusMeasure ≤ ∑ i, eLpNorm (g i) p periodicTorusMeasure := by
  calc eLpNorm f p periodicTorusMeasure
      ≤ eLpNorm (fun y ↦ ∑ i, ‖g i y‖) p periodicTorusMeasure := eLpNorm_mono_real h
    _ = eLpNorm (∑ i : ι, fun y ↦ ‖g i y‖) p periodicTorusMeasure := by
        congr 1; funext y; simp
    _ ≤ ∑ i : ι, eLpNorm (fun y ↦ ‖g i y‖) p periodicTorusMeasure :=
        eLpNorm_sum_le (fun i _ ↦ (hg i).norm) hp
    _ = ∑ i : ι, eLpNorm (g i) p periodicTorusMeasure := by simp [eLpNorm_norm]

/-- `‖∇v‖_{L^p(T³)} ≤ ∑_j ‖∂_j v‖_{L^p(T³)}` (the crude `l² ≤ l¹` bound on the
three tensor columns). -/
theorem periodicLpENorm_gradientTensor_le_sum (v : SpatialField)
    (hv : SmoothPeriodicT v) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    periodicLpENorm p (gradientTensor v) ≤ ∑ j : Fin 3, periodicLpENorm p (dirDeriv j v) := by
  refine eLpNorm_torus_le_sum_of_norm_le hp
    (fun j ↦ (memLp_torusLift_vector (contDiff_dirDeriv hv.1 j).continuous p).aestronglyMeasurable)
    (fun y ↦ ?_)
  exact NSFormalization.Section4.A05.norm_toLp_le_sum
    (fun j ↦ torusLift (dirDeriv j v) y)

/-! ## §6  The explicit constant and the U6 target -/

/-- The explicit U6 constant: the three gradient columns plus the `Λ` term, each
paid for by the order-`1/2` critical constant `CcriticalHalf` of U4. -/
def CcriticalThreeHalves : ℝ := 4 * CcriticalHalf

theorem CcriticalThreeHalves_pos : 0 < CcriticalThreeHalves := by
  unfold CcriticalThreeHalves
  linarith [CcriticalHalf_pos]

/-- **T12 U6, `appendix-a-local-theory.tex:22-26` / `appendix-b-embeddings.tex:26-31`.**
The `gradientLambdaCriticalL3` field of `MeanZeroSobolevCalculusAPI`, verbatim,
with the explicit positive constant `CcriticalThreeHalves = 4 · CcriticalHalf`. -/
theorem gradientLambdaCriticalL3 :
    ∀ (v Lv : SpatialField), SmoothPeriodicT v →
      MemPeriodicHomogeneous (3 / 2) v → IsPeriodicLambda v Lv →
        periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
          ENNReal.ofReal CcriticalThreeHalves *
            periodicHomogeneousENorm (3 / 2) v := by
  intro v Lv hv _hmem hL
  set H : ℝ≥0∞ := periodicHomogeneousENorm (3 / 2) v with hH
  have hgrad : periodicLpENorm 3 (gradientTensor v) ≤
      3 * (ENNReal.ofReal CcriticalHalf * H) := by
    calc periodicLpENorm 3 (gradientTensor v)
        ≤ ∑ j : Fin 3, periodicLpENorm 3 (dirDeriv j v) :=
          periodicLpENorm_gradientTensor_le_sum v hv (by norm_num)
      _ ≤ ∑ _j : Fin 3, ENNReal.ofReal CcriticalHalf * H := by
          refine Finset.sum_le_sum (fun j _ ↦ ?_)
          refine le_trans (velocityCriticalL3_smooth (dirDeriv j v)
            ⟨contDiff_dirDeriv hv.1 j, isPeriodicSpatial_dirDeriv hv.2 j⟩
            (isMeanZeroT_dirDeriv hv j)) ?_
          gcongr
          exact homogeneousENorm_half_dirDeriv_le v hv j
      _ = 3 * (ENNReal.ofReal CcriticalHalf * H) := by
          simp [Finset.sum_const]
  have hlam : periodicLpENorm 3 Lv ≤ ENNReal.ofReal CcriticalHalf * H := by
    refine le_trans (velocityCriticalL3_smooth Lv hL.1 (isMeanZeroT_lambda hL)) ?_
    gcongr
    exact homogeneousENorm_half_lambda_le v Lv hL
  have hconst : ENNReal.ofReal CcriticalThreeHalves = 4 * ENNReal.ofReal CcriticalHalf := by
    unfold CcriticalThreeHalves
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv
      ≤ 3 * (ENNReal.ofReal CcriticalHalf * H) + ENNReal.ofReal CcriticalHalf * H :=
        add_le_add hgrad hlam
    _ = 4 * ENNReal.ofReal CcriticalHalf * H := by ring
    _ = ENNReal.ofReal CcriticalThreeHalves * H := by rw [hconst]

end NSFormalization.Section3.T12
