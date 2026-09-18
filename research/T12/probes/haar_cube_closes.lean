import NSFormalization.Section3.T12.HaarCube
import NSFormalization.Section3.T12.TameProduct

/-!
# Genuine two-mode `L^p` Haar/cube transfer closure probe (lane 366 r1)

This exercises the actual all-`p` transfer `eLpNorm_torusLift_eq_restrict` (and the
`periodicLpENorm` bridge) on the honest two-mode periodic scalar field
`scalarOfCoeff probeCoeff` (`a(x) = 2 cos(2π x₁)`, the field of
`research/T12/probes/tame_product_closes.lean`), at the critical exponents
`p = 3` and `p = 6`.  The witness is nonzero and genuinely two-moded, so neither
the hypotheses nor the transferred equality is vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal BigOperators

/-! ## 1. The two-mode witness `a(x) = 2 cos(2π x₁)` (from `tame_product_closes.lean`) -/

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

/-- The two-mode witness is unit-periodic. -/
theorem probe_periodic : IsPeriodicSpatial (scalarOfCoeff probeCoeff) :=
  (probeMem 2).1

/-! ## 2. Genuine Haar ↔ cube transfer at `p = 3` and `p = 6` on the two-mode field -/

/-- Actual `L³` Haar/cube transfer for the two-mode field (not the definitional
bridge): the Haar norm of the lift equals the cube-restricted Lebesgue norm. -/
example :
    eLpNorm (torusLift (scalarOfCoeff probeCoeff)) 3 periodicTorusMeasure =
      eLpNorm (scalarOfCoeff probeCoeff) 3 (volume.restrict fundamentalCube) :=
  eLpNorm_torusLift_eq_restrict_scalar (scalarOfCoeff probeCoeff) probe_periodic 3

/-- Actual `L⁶` Haar/cube transfer for the two-mode field. -/
example :
    eLpNorm (torusLift (scalarOfCoeff probeCoeff)) 6 periodicTorusMeasure =
      eLpNorm (scalarOfCoeff probeCoeff) 6 (volume.restrict fundamentalCube) :=
  eLpNorm_torusLift_eq_restrict_scalar (scalarOfCoeff probeCoeff) probe_periodic 6

/-- The endpoint `p = ⊤` transfer also holds on the two-mode field. -/
example :
    eLpNorm (torusLift (scalarOfCoeff probeCoeff)) ⊤ periodicTorusMeasure =
      eLpNorm (scalarOfCoeff probeCoeff) ⊤ (volume.restrict fundamentalCube) :=
  eLpNorm_torusLift_eq_restrict_scalar (scalarOfCoeff probeCoeff) probe_periodic ⊤

/-! ## 3. The API `periodicLpENorm` bridged to the cube on the two-mode field -/

/-- `periodicLpENorm 3` of the two-mode field equals its cube-restricted `L³` norm. -/
example :
    periodicLpENorm 3 (scalarOfCoeff probeCoeff) =
      eLpNorm (scalarOfCoeff probeCoeff) 3 (volume.restrict fundamentalCube) :=
  periodicLpENorm_eq_restrict (scalarOfCoeff probeCoeff) probe_periodic 3

/-- `periodicLpENorm 6` of the two-mode field equals its cube-restricted `L⁶` norm. -/
example :
    periodicLpENorm 6 (scalarOfCoeff probeCoeff) =
      eLpNorm (scalarOfCoeff probeCoeff) 6 (volume.restrict fundamentalCube) :=
  periodicLpENorm_eq_restrict (scalarOfCoeff probeCoeff) probe_periodic 6

/-- The definitional API bridge, kept for completeness. -/
example (v : SpatialField) :
    periodicLpENorm 3 v = eLpNorm (torusLift v) 3 periodicTorusMeasure :=
  periodicLpENorm_eq_eLpNorm_torusLift 3 v

/-! ## 4. Non-vacuity: the witness is genuinely two-moded and nonzero -/

/-- Both `±e₀` Fourier coefficients of the witness are one. -/
example :
    periodicFourierCoeff (fun x ↦ ((scalarOfCoeff probeCoeff x : ℝ) : ℂ)) probeFreq = 1 ∧
      periodicFourierCoeff (fun x ↦ ((scalarOfCoeff probeCoeff x : ℝ) : ℂ)) (-probeFreq) = 1 := by
  constructor
  · rw [scalarOfCoeff_coeff probeCoeff_conj probeCoeff_abs_summable probeFreq]
    exact probeCoeff_pos
  · rw [scalarOfCoeff_coeff probeCoeff_conj probeCoeff_abs_summable (-probeFreq)]
    exact probeCoeff_neg

end NSFormalization.Section3.T12
