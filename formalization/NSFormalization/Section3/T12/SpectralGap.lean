import NSFormalization.Section3.T12.MeanZeroCalculus
import NSFormalization.Section3.T10.DatumBasics

/-!
# Spectral comparison for mean-zero periodic Sobolev data

This module compares the inhomogeneous and homogeneous Fourier weights on the
unit three-torus.  It also provides a reusable bounded diagonal reweighting of
the nested `PiLp`/`lp` datum carrier.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open scoped ENNReal BigOperators ComplexConjugate

/-- The explicit spectral-gap constant for the unit-period convention. -/
def gapConst (s : ℝ) : ℝ :=
  (1 + 1 / (4 * Real.pi ^ 2)) ^ (s / 2)

/-- The explicit gap constant is positive at every nonnegative order. -/
theorem gapConst_pos (s : ℝ) (_hs : 0 ≤ s) : 0 < gapConst s := by
  apply Real.rpow_pos_of_pos
  have hpi : 0 < 4 * Real.pi ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
  positivity

private theorem periodicAngularFrequencySq_nonneg (k : PeriodicFrequency) :
    0 ≤ periodicAngularFrequencySq k := by
  unfold periodicAngularFrequencySq
  positivity

private theorem periodicAngularFrequencySq_neg (k : PeriodicFrequency) :
    periodicAngularFrequencySq (-k) = periodicAngularFrequencySq k := by
  simp [periodicAngularFrequencySq]

private theorem periodicFrequencyWeight_pos (k : PeriodicFrequency) :
    0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  have : 0 ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  linarith

private theorem periodicFrequencyWeight_neg (k : PeriodicFrequency) :
    periodicFrequencyWeight (-k) = periodicFrequencyWeight k := by
  simp [periodicFrequencyWeight]

private theorem homogeneousDatumWeight_neg (s : ℝ) (k : PeriodicFrequency) :
    homogeneousDatumWeight s (-k) = homogeneousDatumWeight s k := by
  simp only [homogeneousDatumWeight, neg_eq_zero, periodicAngularFrequencySq_neg]

private theorem one_le_frequency_sq_sum {k : PeriodicFrequency} (hk : k ≠ 0) :
    1 ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  have hki : ∃ i : Fin 3, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  obtain ⟨i, hi⟩ := hki
  have habs : (1 : ℝ) ≤ |(k i : ℝ)| := by
    exact_mod_cast Int.one_le_abs hi
  have hsq : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    simpa only [one_le_sq_iff_one_le_abs] using habs
  exact hsq.trans (Finset.single_le_sum (fun j _ ↦ sq_nonneg (k j : ℝ)) (Finset.mem_univ i))

private theorem periodicAngularFrequencySq_pos {k : PeriodicFrequency} (hk : k ≠ 0) :
    0 < periodicAngularFrequencySq k := by
  unfold periodicAngularFrequencySq
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
    (lt_of_lt_of_le zero_lt_one (one_le_frequency_sq_sum hk))

/-- For nonnegative order, deleting the zero mode and replacing the Bessel
weight by the homogeneous weight is a contraction. -/
theorem homogeneousDatumWeight_le_periodicFrequencyWeight_rpow
    (s : ℝ) (hs : 0 ≤ s) (k : PeriodicFrequency) :
    homogeneousDatumWeight s k ≤ periodicFrequencyWeight k ^ (s / 2) := by
  by_cases hk : k = 0
  · subst k
    simp only [homogeneousDatumWeight, ↓reduceIte]
    exact Real.rpow_nonneg (periodicFrequencyWeight_pos 0).le _
  · simp only [homogeneousDatumWeight, hk, ↓reduceIte]
    apply Real.rpow_le_rpow (periodicAngularFrequencySq_nonneg k) _ (by linarith)
    simp only [periodicAngularFrequencySq, periodicFrequencyWeight]
    linarith

/-- Away from the zero mode, the inhomogeneous weight is bounded by the
explicit gap constant times the homogeneous weight. -/
theorem periodicFrequencyWeight_rpow_le_gap_mul_homogeneous
    (s : ℝ) (hs : 0 ≤ s) (k : PeriodicFrequency) (hk : k ≠ 0) :
    periodicFrequencyWeight k ^ (s / 2) ≤
      gapConst s * homogeneousDatumWeight s k := by
  let c : ℝ := 4 * Real.pi ^ 2
  let x : ℝ := periodicAngularFrequencySq k
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
  have hx : c ≤ x := by
    have h := mul_le_mul_of_nonneg_left (one_le_frequency_sq_sum hk) hc.le
    simpa [c, x, periodicAngularFrequencySq] using h
  have hx0 : 0 ≤ x := hc.le.trans hx
  have hbase : periodicFrequencyWeight k ≤ (1 + 1 / c) * x := by
    have hone : 1 ≤ x / c := (le_div_iff₀ hc).2 (by simpa using hx)
    dsimp [c, x] at hone ⊢
    rw [show periodicFrequencyWeight k = 1 + periodicAngularFrequencySq k by
      simp [periodicFrequencyWeight, periodicAngularFrequencySq]]
    calc
      1 + periodicAngularFrequencySq k ≤
          periodicAngularFrequencySq k / (4 * Real.pi ^ 2) +
            periodicAngularFrequencySq k := by linarith
      _ = (1 + 1 / (4 * Real.pi ^ 2)) * periodicAngularFrequencySq k := by ring
  calc
    periodicFrequencyWeight k ^ (s / 2) ≤
        ((1 + 1 / c) * x) ^ (s / 2) :=
      Real.rpow_le_rpow (periodicFrequencyWeight_pos k).le hbase (by linarith)
    _ = (1 + 1 / c) ^ (s / 2) * x ^ (s / 2) := by
      rw [Real.mul_rpow]
      · positivity
      · exact hx0
    _ = gapConst s * homogeneousDatumWeight s k := by
      simp [gapConst, c, x, homogeneousDatumWeight, hk]

/-- Bounded coordinatewise multiplication on the complete periodic vector
datum carrier.  The bound and its nonnegativity are explicit arguments so the
construction can be reused with different Fourier multipliers. -/
def reweightDatum (w : PeriodicFrequency → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (A : PeriodicVectorData) : PeriodicVectorData :=
  WithLp.toLp 2 (fun i ↦
    ⟨fun k ↦ (w k : ℂ) • A i k,
      by
        have hmem : Memℓp (fun k : PeriodicFrequency ↦ (C : ℂ) • A i k) 2 :=
          (lp.memℓp (A i)).const_smul (C : ℂ)
        exact hmem.mono' (fun k ↦ by
          simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
          exact mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _))⟩)

@[simp]
theorem reweightDatum_apply (w : PeriodicFrequency → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (A : PeriodicVectorData) (i : Fin 3)
    (k : PeriodicFrequency) :
    reweightDatum w C hC hw A i k = (w k : ℂ) • A i k := rfl

/-- A bounded reweighting has operator norm at most its supplied bound. -/
theorem reweightDatum_norm_le (w : PeriodicFrequency → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (A : PeriodicVectorData) :
    ‖reweightDatum w C hC hw A‖ ≤ C * ‖A‖ := by
  have hi : ∀ i : Fin 3,
      ‖reweightDatum w C hC hw A i‖ ≤ C * ‖A i‖ := by
    intro i
    have hpoint : ∀ k : PeriodicFrequency,
        ‖reweightDatum w C hC hw A i k‖ ≤ ‖((C : ℂ) • A i) k‖ := by
      intro k
      simp only [reweightDatum_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _)
    calc
      ‖reweightDatum w C hC hw A i‖ ≤ ‖(C : ℂ) • A i‖ :=
        lp.norm_mono (by norm_num) hpoint
      _ = C * ‖A i‖ := by
        rw [norm_smul]
        congr 1
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  have hsq : ‖reweightDatum w C hC hw A‖ ^ 2 ≤ (C * ‖A‖) ^ 2 := by
    calc
      ‖reweightDatum w C hC hw A‖ ^ 2 =
          ∑ i : Fin 3, ‖reweightDatum w C hC hw A i‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 _ _
      _ ≤ ∑ i : Fin 3, (C * ‖A i‖) ^ 2 := by
        gcongr with i
        exact hi i
      _ = C ^ 2 * ∑ i : Fin 3, ‖A i‖ ^ 2 := by
        simp only [mul_pow]
        rw [Finset.mul_sum]
      _ = (C * ‖A‖) ^ 2 := by
        rw [mul_pow, PiLp.norm_sq_eq_of_L2]
  nlinarith [norm_nonneg (reweightDatum w C hC hw A),
    mul_nonneg hC (norm_nonneg A)]

/-- An even real multiplier preserves the conjugate-reflection real subspace. -/
theorem reweightDatum_real (w : PeriodicFrequency → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (heven : ∀ k, w (-k) = w k)
    (A : realPeriodicSubmodule) :
    reweightDatum w C hC hw A.1 ∈ realPeriodicSubmodule := by
  intro i k
  simp only [reweightDatum_apply]
  change (w (-k) : ℂ) * A.1 i (-k) = star ((w k : ℂ) * A.1 i k)
  rw [heven k, A.2 i k]
  simp

private def homogeneousRatio (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  homogeneousDatumWeight s k / periodicFrequencyWeight k ^ (s / 2)

private def inhomogeneousRatio (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0
  else periodicFrequencyWeight k ^ (s / 2) / homogeneousDatumWeight s k

private theorem homogeneousDatumWeight_nonneg (s : ℝ) (k : PeriodicFrequency) :
    0 ≤ homogeneousDatumWeight s k := by
  by_cases hk : k = 0
  · simp [homogeneousDatumWeight, hk]
  · simp only [homogeneousDatumWeight, hk, ↓reduceIte]
    exact Real.rpow_nonneg (periodicAngularFrequencySq_nonneg k) _

private theorem homogeneousRatio_nonneg (s : ℝ) (k : PeriodicFrequency) :
    0 ≤ homogeneousRatio s k :=
  div_nonneg (homogeneousDatumWeight_nonneg s k)
    (Real.rpow_nonneg (periodicFrequencyWeight_pos k).le _)

private theorem homogeneousRatio_abs_le_one (s : ℝ) (hs : 0 ≤ s)
    (k : PeriodicFrequency) : |homogeneousRatio s k| ≤ 1 := by
  rw [abs_of_nonneg (homogeneousRatio_nonneg s k)]
  exact (div_le_one₀ (Real.rpow_pos_of_pos (periodicFrequencyWeight_pos k) _)).2
    (homogeneousDatumWeight_le_periodicFrequencyWeight_rpow s hs k)

private theorem homogeneousRatio_neg (s : ℝ) (k : PeriodicFrequency) :
    homogeneousRatio s (-k) = homogeneousRatio s k := by
  simp only [homogeneousRatio, homogeneousDatumWeight_neg, periodicFrequencyWeight_neg]

private theorem inhomogeneousRatio_nonneg (s : ℝ) (k : PeriodicFrequency) :
    0 ≤ inhomogeneousRatio s k := by
  by_cases hk : k = 0
  · simp [inhomogeneousRatio, hk]
  · simp only [inhomogeneousRatio, hk, ↓reduceIte]
    exact div_nonneg (Real.rpow_nonneg (periodicFrequencyWeight_pos k).le _)
      (homogeneousDatumWeight_nonneg s k)

private theorem inhomogeneousRatio_abs_le_gap (s : ℝ) (hs : 0 ≤ s)
    (k : PeriodicFrequency) : |inhomogeneousRatio s k| ≤ gapConst s := by
  rw [abs_of_nonneg (inhomogeneousRatio_nonneg s k)]
  by_cases hk : k = 0
  · subst k
    simp [inhomogeneousRatio, (gapConst_pos s hs).le]
  · simp only [inhomogeneousRatio, hk, ↓reduceIte]
    exact (div_le_iff₀ (by
      simp only [homogeneousDatumWeight, hk, ↓reduceIte]
      exact Real.rpow_pos_of_pos (periodicAngularFrequencySq_pos hk) _)).2
        (periodicFrequencyWeight_rpow_le_gap_mul_homogeneous s hs k hk)

private theorem inhomogeneousRatio_neg (s : ℝ) (k : PeriodicFrequency) :
    inhomogeneousRatio s (-k) = inhomogeneousRatio s k := by
  by_cases hk : k = 0
  · subst k
    simp [inhomogeneousRatio]
  · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    simp only [inhomogeneousRatio, hk, hnk, ↓reduceIte,
      periodicFrequencyWeight_neg, homogeneousDatumWeight_neg]

private theorem reweightDatum_enorm_le (w : PeriodicFrequency → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C)
    (A : PeriodicVectorData) :
    ‖reweightDatum w C hC hw A‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ := by
  calc
    ‖reweightDatum w C hC hw A‖ₑ = ENNReal.ofReal ‖reweightDatum w C hC hw A‖ :=
      (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (C * ‖A‖) :=
      ENNReal.ofReal_le_ofReal (reweightDatum_norm_le w C hC hw A)
    _ = ENNReal.ofReal C * ENNReal.ofReal ‖A‖ := ENNReal.ofReal_mul hC
    _ = ENNReal.ofReal C * ‖A‖ₑ := by rw [ofReal_norm]

private theorem homogeneousDatum_unique {s : ℝ} {v : SpatialField}
    (A B : PeriodicSobolev s) (hA : IsPeriodicHomogeneousDatum s v A)
    (hB : IsPeriodicHomogeneousDatum s v B) : A = B := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  rw [hA.2.2.2 i k, hB.2.2.2 i k]

private theorem periodicHomogeneousENorm_eq_enorm {s : ℝ} {v : SpatialField}
    (A : PeriodicSobolev s) (hA : IsPeriodicHomogeneousDatum s v A) :
    periodicHomogeneousENorm s v = ‖A.1‖ₑ := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨A, hA⟩ le_rfl
  · apply le_iInf
    intro B
    rw [homogeneousDatum_unique B.1 A B.2 hA]
    change ‖A.1‖ₑ ≤ ‖A.1‖ₑ
    exact le_rfl

private theorem exists_homogeneousDatum_of_mem {s : ℝ} {v : SpatialField}
    (hv : MemPeriodicHomogeneous s v) :
    ∃ A : PeriodicSobolev s, IsPeriodicHomogeneousDatum s v A := by
  by_contra hnone
  apply hv.2.2.2
  unfold periodicHomogeneousENorm
  apply iInf_eq_top.mpr
  intro A
  exact (hnone ⟨A.1, A.2⟩).elim

/-- On a mean-zero periodic field, the homogeneous extended Sobolev norm is
bounded by the inhomogeneous norm with the sharp comparison constant one. -/
theorem homogeneous_le_sobolev :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicHomogeneousENorm s v ≤ periodicSobolevENorm s v := by
  intro s hs v hv
  unfold periodicSobolevENorm
  apply le_iInf
  intro A
  let B : PeriodicSobolev s :=
    ⟨reweightDatum (homogeneousRatio s) 1 zero_le_one
        (homogeneousRatio_abs_le_one s hs) A.1,
      reweightDatum_real (homogeneousRatio s) 1 zero_le_one
        (homogeneousRatio_abs_le_one s hs) (homogeneousRatio_neg s) A.1⟩
  have hB : IsPeriodicHomogeneousDatum s v B := by
    refine ⟨A.2.1, A.2.2.1, hv.2.2.1, ?_⟩
    intro i k
    change reweightDatum (homogeneousRatio s) 1 zero_le_one
      (homogeneousRatio_abs_le_one s hs) A.1.1 i k = _
    rw [reweightDatum_apply, A.2.2.2 i k]
    have hp : periodicFrequencyWeight k ^ (s / 2) ≠ 0 :=
      (Real.rpow_pos_of_pos (periodicFrequencyWeight_pos k) _).ne'
    change
      ((homogeneousDatumWeight s k / periodicFrequencyWeight k ^ (s / 2) : ℝ) : ℂ) *
          (((periodicFrequencyWeight k ^ (s / 2) : ℝ) : ℂ) *
            periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k) =
        ((homogeneousDatumWeight s k : ℝ) : ℂ) *
          periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k
    rw [← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ hp]
  calc
    periodicHomogeneousENorm s v ≤ ‖B.1‖ₑ :=
      iInf_le_of_le ⟨B, hB⟩ le_rfl
    _ ≤ ‖A.1.1‖ₑ := by
      simpa only [ENNReal.ofReal_one, one_mul] using
        reweightDatum_enorm_le (homogeneousRatio s) 1 zero_le_one
          (homogeneousRatio_abs_le_one s hs) A.1.1

/-- The unit-torus spectral gap: the inhomogeneous norm is bounded by
`(1 + 1/(4π²))^(s/2)` times the homogeneous norm at nonnegative order. -/
theorem spectralGap :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (gapConst s) * periodicHomogeneousENorm s v := by
  intro s hs v hv
  obtain ⟨B, hB⟩ := exists_homogeneousDatum_of_mem hv
  let A : PeriodicSobolev s :=
    ⟨reweightDatum (inhomogeneousRatio s) (gapConst s) (gapConst_pos s hs).le
        (inhomogeneousRatio_abs_le_gap s hs) B.1,
      reweightDatum_real (inhomogeneousRatio s) (gapConst s) (gapConst_pos s hs).le
        (inhomogeneousRatio_abs_le_gap s hs) (inhomogeneousRatio_neg s) B⟩
  have hA : IsPeriodicDatum s v A := by
    refine ⟨hB.1, hB.2.1, ?_⟩
    intro i k
    change reweightDatum (inhomogeneousRatio s) (gapConst s) (gapConst_pos s hs).le
      (inhomogeneousRatio_abs_le_gap s hs) B.1 i k = _
    rw [reweightDatum_apply]
    by_cases hk : k = 0
    · subst k
      have hzero : periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) 0 = 0 := by
        rw [periodicFourierCoeff_zero_eq_mean_component hB.2.1 i, hB.2.2.1]
        rfl
      simp [inhomogeneousRatio, hzero]
    · rw [hB.2.2.2 i k]
      have hh : homogeneousDatumWeight s k ≠ 0 := by
        simp only [homogeneousDatumWeight, hk, ↓reduceIte]
        exact (Real.rpow_pos_of_pos (periodicAngularFrequencySq_pos hk) _).ne'
      simp only [inhomogeneousRatio, hk, ↓reduceIte]
      change
        ((periodicFrequencyWeight k ^ (s / 2) / homogeneousDatumWeight s k : ℝ) : ℂ) *
            (((homogeneousDatumWeight s k : ℝ) : ℂ) *
              periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k) =
          ((periodicFrequencyWeight k ^ (s / 2) : ℝ) : ℂ) *
            periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k
      rw [← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ hh]
  calc
    periodicSobolevENorm s v ≤ ‖A.1‖ₑ :=
      iInf_le_of_le ⟨A, hA⟩ le_rfl
    _ ≤ ENNReal.ofReal (gapConst s) * ‖B.1‖ₑ :=
      reweightDatum_enorm_le (inhomogeneousRatio s) (gapConst s)
        (gapConst_pos s hs).le (inhomogeneousRatio_abs_le_gap s hs) B.1
    _ = ENNReal.ofReal (gapConst s) * periodicHomogeneousENorm s v := by
      rw [periodicHomogeneousENorm_eq_enorm B hB]

end NSFormalization.Section3.T12
