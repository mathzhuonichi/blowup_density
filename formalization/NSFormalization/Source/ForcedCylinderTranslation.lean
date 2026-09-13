import NSFormalization.Source.ForcedCylinderLocal

/-! Translation covariance adapters for the actual source cylinder operators.
No existence or ordinary-space descent assertion is made here. -/
noncomputable section
namespace NSFormalization.Source.ForcedCylinderLocal
open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevTransport
open EulerSobolevL2Product EulerSobolevHeat EulerGaussianCylinderHeat

open scoped NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The value of a translated Sobolev field is its actual L2 translation. -/
theorem translation_value {q : ℕ} (a : LiftDomain period) (u : SobolevSpace period q) :
    value period (sobolevTranslation period q a u) = translation period a (value period u) := rfl

/-- One-step restriction commutes with cylinder translation. -/
theorem truncate_translation {q : ℕ} (a : LiftDomain period)
    (u : SobolevSpace period (q + 1)) :
    truncateOperator period q (sobolevTranslation period (q + 1) a u) =
      sobolevTranslation period q a (truncateOperator period q u) := by
  apply value_injective period
  rfl

/-- The genuine finite-order spatial advection is translation covariant. -/
theorem advection_translation {q : ℕ} (hq : 6 ≤ q) (a : LiftDomain period)
    (u v : SobolevSpace period (q + 1)) :
    advection period hq (sobolevTranslation period (q + 1) a u)
        (sobolevTranslation period (q + 1) a v) =
      sobolevTranslation period q a (advection period hq u v) := by
  apply value_injective period
  simp only [advection, transportBilinear_value, translation_value,
    truncate_translation, derivativeOperator_translation]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact scalarProduct_translation period (by omega) _ a _ _

/-- The actual Leray projection commutes with cylinder translation. -/
theorem leray_translation {q : ℕ} (a : LiftDomain period) (u : SobolevSpace period q) :
    leray period q (sobolevTranslation period q a u) =
      sobolevTranslation period q a (leray period q u) := by
  apply value_injective period
  simp only [leray_value, translation_value, map_sub, gradientProjection_translation]

/-- The source heat operator commutes with cylinder translation at every variance. -/
theorem heatOperator_translation {q : ℕ} (v : ℝ≥0) (a : LiftDomain period)
    (u : SobolevSpace period q) :
    heatOperator period q v (sobolevTranslation period q a u) =
      sobolevTranslation period q a (heatOperator period q v u) := by
  apply value_injective period
  simp only [heatOperator_value, translation_value, cylinderHeat_translation]

/-- Positive-variance heat gain commutes with cylinder translation. -/
theorem heatGain_translation {q : ℕ} (v : ℝ≥0) (hv : 0 < v) (a : LiftDomain period)
    (u : SobolevSpace period q) :
    heatGain period q v hv (sobolevTranslation period q a u) =
      sobolevTranslation period (q + 1) a (heatGain period q v hv u) := by
  apply value_injective period
  simp only [heatGain_value, translation_value, cylinderHeat_translation]

/-- The actual time kernel is covariant, including its nonpositive-time zero branch. -/
theorem heatKernel_translation {q : ℕ} (ν : ℝ) (hν : 0 < ν) (t : ℝ)
    (a : LiftDomain period) (u : SobolevSpace period q) :
    heatKernel period q ν hν t (sobolevTranslation period q a u) =
      sobolevTranslation period (q + 1) a (heatKernel period q ν hν t u) := by
  by_cases ht : 0 < t
  · simp only [heatKernel, dite_eq_left ht]
    exact heatGain_translation period _ _ a u
  · simp only [heatKernel, dite_eq_right ht, zero_apply, map_zero]

end NSFormalization.Source.ForcedCylinderLocal
