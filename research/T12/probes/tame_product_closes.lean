import NSFormalization.Section3.T12.TameProduct

/-!
# Exact API-field closure probes for the periodic scalar tame product

`Cproduct := tameProductConst`.  The last section exhibits a genuine two-mode
witness, so neither the hypotheses nor the conclusion are vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal BigOperators

/-! ## 1. The two API fields, verbatim -/

/-- The `Cproduct_pos` API field, verbatim. -/
example : ∀ m : ℕ, 0 < tameProductConst m := tameProductConst_pos

/-- The `tameProduct` API field, verbatim. -/
example :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : Space → ℝ,
      MemPeriodicHmScalar m a → MemPeriodicHmScalar m b →
        periodicScalarSobolevENorm (m : ℝ) (fun x ↦ a x * b x) ≤
          ENNReal.ofReal (tameProductConst m) *
            (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (m : ℝ) b +
              periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (m : ℝ) a) :=
  tameProduct

/-! ## 2. A two-mode non-vacuity witness

`a(x) = 2 cos(2π x₁)` — the real scalar whose only nonzero Fourier modes are
`±e₀`, both equal to one. -/

/-- The first lattice basis vector. -/
def probeFreq : PeriodicFrequency := fun i ↦ if i = 0 then 1 else 0

theorem probeFreq_ne_neg : probeFreq ≠ -probeFreq := by
  intro h
  have h0 := congrFun h 0
  simp [probeFreq, Pi.neg_apply] at h0

/-- The two-mode coefficient family, supported exactly on `{e₀, -e₀}`. -/
def probeCoeff (k : PeriodicFrequency) : ℂ :=
  if k = probeFreq then 1 else if k = -probeFreq then 1 else 0

theorem probeCoeff_eq_zero {k : PeriodicFrequency} (h1 : k ≠ probeFreq)
    (h2 : k ≠ -probeFreq) : probeCoeff k = 0 := by
  simp [probeCoeff, h1, h2]

theorem probeCoeff_pos : probeCoeff probeFreq = 1 := by simp [probeCoeff]

theorem probeCoeff_neg : probeCoeff (-probeFreq) = 1 := by
  have hne : -probeFreq ≠ probeFreq := fun h ↦ probeFreq_ne_neg h.symm
  simp [probeCoeff, hne]

/-- Every function vanishing off the two modes is summable. -/
theorem probeSummable (g : PeriodicFrequency → ℝ)
    (hg : ∀ k, k ≠ probeFreq → k ≠ -probeFreq → g k = 0) : Summable g := by
  classical
  refine summable_of_ne_finset_zero (s := ({probeFreq, -probeFreq} : Finset PeriodicFrequency)) ?_
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact hg k hk.1 hk.2

theorem probeCoeff_conj : ∀ k : PeriodicFrequency, probeCoeff (-k) = star (probeCoeff k) := by
  intro k
  have hne : -probeFreq ≠ probeFreq := fun h ↦ probeFreq_ne_neg h.symm
  by_cases h1 : k = probeFreq
  · subst h1
    rw [probeCoeff_neg, probeCoeff_pos]
    simp
  · by_cases h2 : k = -probeFreq
    · subst h2
      rw [neg_neg, probeCoeff_pos, probeCoeff_neg]
      simp
    · have h3 : -k ≠ probeFreq := by
        intro h
        exact h2 (by rw [← neg_neg k, h])
      have h4 : -k ≠ -probeFreq := fun h ↦ h1 (neg_injective h)
      rw [probeCoeff_eq_zero h3 h4, probeCoeff_eq_zero h1 h2]
      simp

theorem probeCoeff_abs_summable : Summable fun k ↦ ‖probeCoeff k‖ :=
  probeSummable _ fun k h1 h2 ↦ by rw [probeCoeff_eq_zero h1 h2, norm_zero]

theorem probeCoeff_contDiff : ContDiff ℝ (⊤ : ℕ∞) (torusScalarSeries probeCoeff) := by
  refine torusScalarSeries_contDiff fun N ↦ probeSummable _ fun k h1 h2 ↦ ?_
  rw [probeCoeff_eq_zero h1 h2, norm_zero, mul_zero]

theorem probeCoeff_weighted (m : ℕ) :
    Summable fun k ↦ (periodicFrequencyWeight k ^ ((m : ℝ) / 2) * ‖probeCoeff k‖) ^ 2 :=
  probeSummable _ fun k h1 h2 ↦ by
    rw [probeCoeff_eq_zero h1 h2, norm_zero, mul_zero, sq, mul_zero]

/-- The witness is in `H^m(T³)` for every order `m`. -/
theorem probeMem (m : ℕ) : MemPeriodicHmScalar m (scalarOfCoeff probeCoeff) :=
  memPeriodicHmScalar_ofCoeff probeCoeff_conj probeCoeff_abs_summable
    probeCoeff_contDiff.continuous (probeCoeff_weighted m)

/-- The witness is genuinely two-moded: both `±e₀` coefficients are one. -/
example :
    periodicFourierCoeff (fun x ↦ ((scalarOfCoeff probeCoeff x : ℝ) : ℂ)) probeFreq = 1 ∧
      periodicFourierCoeff (fun x ↦ ((scalarOfCoeff probeCoeff x : ℝ) : ℂ))
        (-probeFreq) = 1 := by
  constructor
  · rw [scalarOfCoeff_coeff probeCoeff_conj probeCoeff_abs_summable probeFreq]
    exact probeCoeff_pos
  · rw [scalarOfCoeff_coeff probeCoeff_conj probeCoeff_abs_summable (-probeFreq)]
    exact probeCoeff_neg

/-- In particular the witness is not the zero field. -/
example : scalarOfCoeff probeCoeff ≠ (fun _ ↦ (0 : ℝ)) := by
  intro h
  have h1 : periodicFourierCoeff
      (fun x ↦ ((scalarOfCoeff probeCoeff x : ℝ) : ℂ)) probeFreq = 1 := by
    rw [scalarOfCoeff_coeff probeCoeff_conj probeCoeff_abs_summable probeFreq]
    exact probeCoeff_pos
  rw [h] at h1
  simp only [Complex.ofReal_zero] at h1
  rw [periodicFourierCoeff_const 0 probeFreq] at h1
  simp at h1

/-- The tame product, instantiated at the two-mode witness: the hypotheses are
met by an honest nonzero field, so the field is non-vacuous. -/
example (m : ℕ) (hm : 2 ≤ m) :
    periodicScalarSobolevENorm (m : ℝ)
        (fun x ↦ scalarOfCoeff probeCoeff x * scalarOfCoeff probeCoeff x) ≤
      ENNReal.ofReal (tameProductConst m) *
        (periodicScalarSobolevENorm 2 (scalarOfCoeff probeCoeff) *
            periodicScalarSobolevENorm (m : ℝ) (scalarOfCoeff probeCoeff) +
          periodicScalarSobolevENorm 2 (scalarOfCoeff probeCoeff) *
            periodicScalarSobolevENorm (m : ℝ) (scalarOfCoeff probeCoeff)) :=
  tameProduct m hm _ _ (probeMem m) (probeMem m)

end NSFormalization.Section3.T12
