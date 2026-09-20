import NSFormalization.Section3.T10.PeriodicData
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The periodic Leray projector

The coordinate symbol in `PeriodicData` is realized frequency by frequency as
the orthogonal projection onto the complement of the complexified frequency
vector.  Its Hilbert-space contraction gives summability of the transposed
coordinate sequences and the exact `WithLp 2` norm bound.
-/

noncomputable section

namespace NSFormalization.Section3.T10

open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace

private abbrev FrequencyVector := EuclideanSpace ℂ (Fin 3)

private def frequencyVector (k : PeriodicFrequency) : FrequencyVector :=
  WithLp.toLp 2 (fun i ↦ (k i : ℂ))

private def coefficientVector {s : ℝ} (A : PeriodicSobolev s)
    (k : PeriodicFrequency) : FrequencyVector :=
  WithLp.toLp 2 (fun i ↦ A.1 i k)

private def lerayVector (k : PeriodicFrequency) (v : FrequencyVector) : FrequencyVector :=
  if k = 0 then v else (Submodule.orthogonal (ℂ ∙ frequencyVector k)).starProjection v

private lemma periodicLeray_eq_lerayVector (s : ℝ) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicLeray s A i k = lerayVector k (coefficientVector A k) i := by
  by_cases hk : k = 0
  · simp [periodicLeray, lerayVector, hk, coefficientVector]
  · simp only [periodicLeray, lerayVector, hk, ↓reduceIte]
    have h := (ℂ ∙ frequencyVector k).starProjection_add_starProjection_orthogonal
      (coefficientVector A k)
    rw [Submodule.starProjection_singleton] at h
    have hv : (Submodule.orthogonal (ℂ ∙ frequencyVector k)).starProjection
        (coefficientVector A k) = coefficientVector A k -
          (⟪frequencyVector k, coefficientVector A k⟫_ℂ /
            (((‖frequencyVector k‖ ^ 2 : ℝ) : ℂ))) • frequencyVector k := by
      apply (eq_sub_iff_add_eq).2
      simpa [add_comm] using h
    rw [hv]
    simp only [PiLp.sub_apply, PiLp.smul_apply]
    rw [show ⟪frequencyVector k, coefficientVector A k⟫_ℂ =
        ∑ j : Fin 3, (k j : ℂ) * A.1 j k by
          rw [PiLp.inner_apply]
          apply Finset.sum_congr rfl
          intro j _
          simp [frequencyVector, coefficientVector, RCLike.inner_apply, mul_comm]]
    rw [show ‖frequencyVector k‖ ^ 2 = ∑ j : Fin 3, (k j : ℝ) ^ 2 by
          rw [PiLp.norm_sq_eq_of_L2]
          apply Finset.sum_congr rfl
          intro j _
          simp [frequencyVector, Complex.norm_intCast, sq_abs]]
    simp only [coefficientVector, frequencyVector, WithLp.ofLp_toLp]
    ring

private lemma periodicLeray_neg (s : ℝ) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicLeray s A i (-k) = star (periodicLeray s A i k) := by
  by_cases hk : k = 0
  · subst k
    simpa [periodicLeray] using A.2 i 0
  · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    simp only [periodicLeray, hnk, hk, ↓reduceIte]
    rw [A.2 i k]
    have hsum : (∑ j : Fin 3, ((-k) j : ℂ) * A.1 j (-k)) =
        ∑ j : Fin 3, ((-k) j : ℂ) * star (A.1 j k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [A.2 j k]
    rw [hsum]
    simp only [Pi.neg_apply, Int.cast_neg, neg_sq, star_sub, star_mul, star_sum]
    simp
    simp only [mul_comm]
    ring

private lemma lerayVector_norm_le (k : PeriodicFrequency) (v : FrequencyVector) :
    ‖lerayVector k v‖ ≤ ‖v‖ := by
  by_cases hk : k = 0
  · simp [lerayVector, hk]
  · simp only [lerayVector, hk, ↓reduceIte]
    exact (Submodule.orthogonal (ℂ ∙ frequencyVector k)).norm_starProjection_apply_le v

private lemma lerayVector_component_sq_le (k : PeriodicFrequency) (v : FrequencyVector)
    (i : Fin 3) :
    ‖lerayVector k v i‖ ^ 2 ≤ ∑ j : Fin 3, ‖v j‖ ^ 2 := by
  calc
    ‖lerayVector k v i‖ ^ 2 ≤ ‖lerayVector k v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      exact Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖lerayVector k v j‖)
        (Finset.mem_univ i)
    _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (lerayVector_norm_le k v) 2
    _ = ∑ j : Fin 3, ‖v j‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _

private lemma inner_frequency_lerayVector (k : PeriodicFrequency) (v : FrequencyVector) :
    ⟪frequencyVector k, lerayVector k v⟫_ℂ = 0 := by
  by_cases hk : k = 0
  · subst k
    have hzero : frequencyVector 0 = 0 := by
      apply PiLp.ext
      intro i
      simp [frequencyVector]
    rw [hzero, inner_zero_left]
  · simp only [lerayVector, hk, ↓reduceIte]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      ((Submodule.orthogonal (ℂ ∙ frequencyVector k)).starProjection_apply_mem v)

private lemma sum_frequency_lerayVector (k : PeriodicFrequency) (v : FrequencyVector) :
    ∑ j : Fin 3, (k j : ℂ) * lerayVector k v j = 0 := by
  rw [← inner_frequency_lerayVector k v]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp [frequencyVector, RCLike.inner_apply, mul_comm]

private lemma lerayVector_eq_self_of_inner_eq_zero
    (k : PeriodicFrequency) (v : FrequencyVector)
    (h : ⟪frequencyVector k, v⟫_ℂ = 0) : lerayVector k v = v := by
  by_cases hk : k = 0
  · simp [lerayVector, hk]
  · simp only [lerayVector, hk, ↓reduceIte]
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr h)

private lemma periodicLeray_solenoidal {s : ℝ} {A B : PeriodicSobolev s}
    (hAB : IsPeriodicLerayDatum A B) : IsSolenoidalPeriodicDatum B := by
  intro k
  calc
    _ = ∑ j : Fin 3, periodicDerivativeSymbol j k * periodicLeray s A j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hAB j k]
    _ = (2 * Real.pi * Complex.I) *
        ∑ j : Fin 3, (k j : ℂ) * lerayVector k (coefficientVector A k) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [periodicLeray_eq_lerayVector]
      simp only [periodicDerivativeSymbol]
      ring
    _ = 0 := by rw [sum_frequency_lerayVector, mul_zero]

/-- Every solenoidal periodic datum is fixed coefficientwise by the periodic
Leray symbol. -/
theorem periodicLeray_of_solenoidal {s : ℝ} (A : PeriodicSobolev s) :
    IsSolenoidalPeriodicDatum A →
      ∀ (i : Fin 3) (k : PeriodicFrequency), periodicLeray s A i k = A.1 i k := by
  intro hA i k
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hdot : ∑ j : Fin 3, (k j : ℂ) * A.1 j k = 0 := by
    have h := hA k
    have heq : (∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k) =
        (2 * Real.pi * Complex.I) * ∑ j : Fin 3, (k j : ℂ) * A.1 j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [periodicDerivativeSymbol]
      ring
    rw [heq] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  rw [periodicLeray_eq_lerayVector]
  have hinner : ⟪frequencyVector k, coefficientVector A k⟫_ℂ = 0 := by
    rw [PiLp.inner_apply]
    simpa [frequencyVector, coefficientVector, RCLike.inner_apply, mul_comm] using hdot
  rw [lerayVector_eq_self_of_inner_eq_zero k (coefficientVector A k) hinner]
  rfl

/-- The coefficient formula defines a same-order real periodic Sobolev datum,
is a contraction, and has solenoidal range. -/
theorem leray_exists_contraction :
    ∀ (s : ℝ) (A : PeriodicSobolev s),
      ∃ B : PeriodicSobolev s,
        IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ ‖A‖ ∧ IsSolenoidalPeriodicDatum B := by
  intro s A
  have hA (i : Fin 3) : Summable (fun k : PeriodicFrequency ↦ ‖A.1 i k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (A.1 i)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have henergy : Summable (fun k : PeriodicFrequency ↦ ∑ i : Fin 3, ‖A.1 i k‖ ^ 2) :=
    summable_sum (fun i _ ↦ hA i)
  have hbmem (i : Fin 3) :
      Memℓp (fun k : PeriodicFrequency ↦ lerayVector k (coefficientVector A k) i) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Summable.of_nonneg_of_le
        (fun k ↦ sq_nonneg ‖lerayVector k (coefficientVector A k) i‖)
        (fun k ↦ by
          simpa only [coefficientVector, WithLp.ofLp_toLp] using
            lerayVector_component_sq_le k (coefficientVector A k) i)
        henergy
  let bcomp : Fin 3 → PeriodicScalarData := fun i ↦
    ⟨fun k ↦ lerayVector k (coefficientVector A k) i, hbmem i⟩
  let bvec : PeriodicVectorData := WithLp.toLp 2 bcomp
  have hreal : bvec ∈ realPeriodicSubmodule := by
    intro i k
    change lerayVector (-k) (coefficientVector A (-k)) i =
      star (lerayVector k (coefficientVector A k) i)
    rw [← periodicLeray_eq_lerayVector s A i (-k),
      ← periodicLeray_eq_lerayVector s A i k]
    exact periodicLeray_neg s A i k
  let B : PeriodicSobolev s := ⟨bvec, hreal⟩
  have hbNorm (i : Fin 3) : ‖bcomp i‖ ^ 2 =
      ∑' k : PeriodicFrequency, ‖lerayVector k (coefficientVector A k) i‖ ^ 2 := by
    simpa only [bcomp, ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (bcomp i)
  have hANorm (i : Fin 3) : ‖A.1 i‖ ^ 2 =
      ∑' k : PeriodicFrequency, ‖A.1 i k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (A.1 i)
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i k
    change lerayVector k (coefficientVector A k) i = periodicLeray s A i k
    exact (periodicLeray_eq_lerayVector s A i k).symm
  · apply (sq_le_sq₀ (norm_nonneg B) (norm_nonneg A)).mp
    change ‖bvec‖ ^ 2 ≤ ‖A.1‖ ^ 2
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    change (∑ i : Fin 3, ‖bcomp i‖ ^ 2) ≤ ∑ i : Fin 3, ‖A.1 i‖ ^ 2
    simp_rw [hbNorm, hANorm]
    rw [← Summable.tsum_finsetSum (fun i _ ↦ by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hbmem i).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))]
    rw [← Summable.tsum_finsetSum (fun i _ ↦ hA i)]
    apply Summable.tsum_le_tsum
    · intro k
      calc
        (∑ i : Fin 3, ‖lerayVector k (coefficientVector A k) i‖ ^ 2) =
            ‖lerayVector k (coefficientVector A k)‖ ^ 2 :=
          (PiLp.norm_sq_eq_of_L2 _ _).symm
        _ ≤ ‖coefficientVector A k‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
          (lerayVector_norm_le k (coefficientVector A k)) 2
        _ = ∑ i : Fin 3, ‖A.1 i k‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
          rfl
    · exact summable_sum (fun i _ ↦
        (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (hbmem i).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)))
    · exact henergy
  · intro k
    change ∑ j : Fin 3, periodicDerivativeSymbol j k *
      lerayVector k (coefficientVector A k) j = 0
    calc
      _ = (2 * Real.pi * Complex.I) *
          ∑ j : Fin 3, (k j : ℂ) * lerayVector k (coefficientVector A k) j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            simp only [periodicDerivativeSymbol]
            ring
      _ = 0 := by rw [sum_frequency_lerayVector, mul_zero]

/-- Applying the periodic Leray graph twice gives the same datum as applying it
once. -/
theorem leray_projector :
    ∀ (s : ℝ) (A B C : PeriodicSobolev s),
      IsPeriodicLerayDatum A B → IsPeriodicLerayDatum B C → C = B := by
  intro s A B C hAB hBC
  have hsol : IsSolenoidalPeriodicDatum B := periodicLeray_solenoidal hAB
  apply Subtype.ext
  apply PiLp.ext
  intro i
  apply lp.ext
  funext k
  rw [hBC i k]
  exact periodicLeray_of_solenoidal B hsol i k

/-- The theorem is inhabited on the concrete zero periodic field. -/
example (s : ℝ) :
    ∃ B : PeriodicSobolev s,
      IsPeriodicLerayDatum (0 : PeriodicSobolev s) B ∧
        ‖B‖ ≤ ‖(0 : PeriodicSobolev s)‖ ∧ IsSolenoidalPeriodicDatum B :=
  leray_exists_contraction s 0

end NSFormalization.Section3.T10
