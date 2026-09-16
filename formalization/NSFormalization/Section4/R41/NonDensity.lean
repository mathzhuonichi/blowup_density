import NSFormalization.Section4.R41.NonDensityL2
import NSFormalization.Paper3.Thresholds

/-! Theorem 4.1(ii), the non-density direction simultaneously for `q = 1, 2`.

The manuscript and the proposed `RMainAPI` use a real exponent `q`, whereas
`forceSobolevENorm` uses an `ENNReal` exponent.  We retain the API's real
binder and use `ENNReal.ofReal q`; in the two admitted cases this is exactly
the existing `q = 1` or `q = 2` norm.

`RMainThresholds` is the formalization-side copy of the frozen
`Contracts.V1.ThresholdAPI`.  Its formula is copied verbatim, and
`rMainThresholds` uses `Paper3.forceExponent`, the same implementation selected
by the registered threshold binding.  The verification-side conformance file
records the resulting `rfl` exponent bridge. -/
noncomputable section
open scoped ENNReal

namespace NSFormalization.Section4.R41
open A02 (SpaceTimeField)
open D01

/-- Formalization-side copy of the threshold-arithmetic contract used by the
proposed `RMainAPI`. -/
structure RMainThresholds where
  exponent : ℝ → ℝ → ℝ
  formula : ∀ q s : ℝ, exponent q s = 2 / q - 3 / 2 - s
  positive : ∀ q s : ℝ, 0 < exponent q s ↔ s < 2 / q - 3 / 2
  l1 : ∀ s : ℝ, exponent 1 s = 1 / 2 - s
  l2 : ∀ s : ℝ, exponent 2 s = -1 / 2 - s
  negativeIndex : ∀ s : ℝ, s < -1 / 2 →
    ∃ r : ℝ, -3 / 2 < r ∧ r < -1 / 2 ∧ s < r
  energy : exponent 1 0 = 1 / 2 ∧ exponent 2 (-1) = 1 / 2

/-- The local threshold value uses the same exponent and arithmetic witnesses
as the registered `Bindings.thresholds`. -/
def rMainThresholds : RMainThresholds where
  exponent := Paper3.forceExponent
  formula := fun _ _ => rfl
  positive := Paper3.forceExponent_pos_iff
  l1 := Paper3.forceExponent_one
  l2 := Paper3.forceExponent_two
  negativeIndex := fun _ hs => Paper3.negative_intermediate_index hs
  energy := Paper3.energy_force_exponents

/-- `RMainAPI.nonDensityZero` for either allowed exponent.  The two witnesses
are explicit: `R43.criticalConst * ν` for `q = 1`, and `R44.radius ν T` for
`q = 2`. -/
theorem nonDensityZero_of_q (thresholds : RMainThresholds) :
    ∀ q : ℝ, (q = 1 ∨ q = 2) →
      ∀ ν T : ℝ, 0 < ν → 0 < T →
        ∀ s : ℝ, thresholds.exponent q 0 ≤ s →
          ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ breakdownSetRZero ν T,
            ENNReal.ofReal ρ ≤ forceSobolevENorm (ENNReal.ofReal q) s f := by
  rintro q (rfl | rfl) ν T hν hT s hs
  · have hs' : 1 / 2 ≤ s := by
      rw [thresholds.l1] at hs
      norm_num at hs ⊢
      exact hs
    refine ⟨R43.criticalConst * ν, mul_pos R43.criticalConst_pos hν, ?_⟩
    intro f hf
    simpa using criticalRadius_le_forceSobolevENorm hν hs' hf
  · have hs' : -1 / 2 ≤ s := by
      rw [thresholds.l2] at hs
      norm_num at hs ⊢
      exact hs
    refine ⟨R44.radius ν T, R44.radius_pos hν, ?_⟩
    intro f hf
    simpa using radius_le_forceSobolevENorm_L2 hν hT hs' hf

/-- Theorem 4.1(ii), the only-if direction at zero initial velocity, for either
`q = 1` or `q = 2`. -/
theorem not_breakdownDenseR_zero_of_q (thresholds : RMainThresholds) :
    ∀ q : ℝ, (q = 1 ∨ q = 2) →
      ∀ ν T : ℝ, 0 < ν → 0 < T →
        ∀ s : ℝ, thresholds.exponent q 0 ≤ s →
          ¬ BreakdownDenseR ν (fun _ => 0) T (ENNReal.ofReal q) s := by
  rintro q (rfl | rfl) ν T hν hT s hs
  · have hs' : 1 / 2 ≤ s := by
      rw [thresholds.l1] at hs
      norm_num at hs ⊢
      exact hs
    simpa using not_breakdownDenseR_zero_L1 ν T hν hT s hs'
  · have hs' : -1 / 2 ≤ s := by
      rw [thresholds.l2] at hs
      norm_num at hs ⊢
      exact hs
    simpa using not_breakdownDenseR_zero_L2 ν T hν hT s hs'

/-- The proved `nonDensityZero` fragment of the proposed `RMainAPI`, retaining
the skeleton's binder order and its threshold value without claiming any of
the density or insertion-rider fields. -/
structure RMainNonDensity where
  ν : ℝ
  T : ℝ
  hν : 0 < ν
  hT : 0 < T
  q : ℝ
  hq : q = 1 ∨ q = 2
  thresholds : RMainThresholds
  nonDensityZero :
    ∀ s : ℝ, thresholds.exponent q 0 ≤ s →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ f : SpaceTimeField, f ∈ breakdownSetRZero ν T →
        ENNReal.ofReal ρ ≤ forceSobolevENorm (ENNReal.ofReal q) s f

example : RMainNonDensity :=
  ⟨1, 1, by norm_num, by norm_num, 1, Or.inl rfl, rMainThresholds,
    nonDensityZero_of_q rMainThresholds 1 (Or.inl rfl) 1 1
      (by norm_num) (by norm_num)⟩

example : RMainNonDensity :=
  ⟨1, 1, by norm_num, by norm_num, 2, Or.inr rfl, rMainThresholds,
    nonDensityZero_of_q rMainThresholds 2 (Or.inr rfl) 1 1
      (by norm_num) (by norm_num)⟩

example : ¬ BreakdownDenseR 1 (fun _ => 0) 1 (ENNReal.ofReal (1 : ℝ)) (1 / 2) :=
  not_breakdownDenseR_zero_of_q rMainThresholds 1 (Or.inl rfl) 1 1
    (by norm_num) (by norm_num) (1 / 2)
    (by norm_num [rMainThresholds, Paper3.forceExponent])

example : ¬ BreakdownDenseR 1 (fun _ => 0) 1 (ENNReal.ofReal (2 : ℝ)) (-1 / 2) :=
  not_breakdownDenseR_zero_of_q rMainThresholds 2 (Or.inr rfl) 1 1
    (by norm_num) (by norm_num) (-1 / 2)
    (by norm_num [rMainThresholds, Paper3.forceExponent])

end NSFormalization.Section4.R41
