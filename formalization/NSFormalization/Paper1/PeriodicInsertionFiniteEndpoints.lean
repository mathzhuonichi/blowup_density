import NSFormalization.Paper1.PeriodicForceFiniteEndpoints
import NSFormalization.Paper1.PeriodicInsertionEndpointRateBound

/-!
# Finite endpoint gauges for the actual insertion family

The endpoint assembly already gives eventual finite bounds for the genuine
whole-space insertion force after periodization.  This file only bridges
those bounds to the `forceDistance` gauge at the two integer endpoints.  The
statement is consequently eventual in the insertion scale and retains all
smoothness and compact-support hypotheses of the insertion construction.
No finiteness assertion is made for an arbitrary abstract `IsTestForce`.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicInsertionFiniteEndpoints

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicInsertionEndpointRateBound
open NSFormalization.Paper1.PeriodicForceConvergence
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal FourierTransform Topology

private theorem insertion_endpoint_rhs_zero_lt_top
    {ε : ℝ} {C₀ C₁ : ℝ≥0∞} (hC₀ : C₀ < (⊤ : ℝ≥0∞)) :
    3 * ((ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀) ^ (1 - (0 : ℝ)) *
      (ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁)) ^ (0 : ℝ)) <
      (⊤ : ℝ≥0∞) := by
  simp only [sub_zero, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one]
  have hprod : ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀ <
      (⊤ : ℝ≥0∞) := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC₀
  exact ENNReal.mul_lt_top (by norm_num) hprod

private theorem insertion_endpoint_rhs_one_lt_top
    {ε : ℝ} {C₀ C₁ : ℝ≥0∞} (hC₁ : C₁ < (⊤ : ℝ≥0∞)) :
    3 * ((ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₀) ^ (1 - (1 : ℝ)) *
      (ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁)) ^ (1 : ℝ)) <
      (⊤ : ℝ≥0∞) := by
  simp only [sub_self, ENNReal.rpow_zero, ENNReal.rpow_one, one_mul]
  have hprod : ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁ <
      (⊤ : ℝ≥0∞) := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC₁
  have hprod' : ENNReal.ofReal (2 * Real.pi) *
      (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * C₁) <
      (⊤ : ℝ≥0∞) := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hprod
  exact ENNReal.mul_lt_top (by norm_num) hprod'

/-- The genuine periodized insertion force has finite zero-order distance
from the zero force for all sufficiently small positive scales. -/
theorem eventually_forceDistance_lt_top_actual_insertion_periodized_zero
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      forceDistance 0
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) 0 <
          (⊤ : ℝ≥0∞) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hb⟩ :=
    eventually_actual_insertion_vector_periodized_endpoint_bound
      ν hf hfc hv T hθ hη hθc hηc (s := (0 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [hb] with ε hε
  have hfin := insertion_endpoint_rhs_zero_lt_top
    (ε := ε) (C₀ := C₀) (C₁ := C₁) hC₀
  have hdist :
      eLpNorm (fun t => periodicVectorSobolevNorm 0
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume <
        (⊤ : ℝ≥0∞) := hε.trans_lt hfin
  calc
    forceDistance 0
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) 0 =
        eLpNorm (fun t => periodicVectorSobolevNorm 0
          (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume := by
      simpa only [Pi.zero_apply, zero_add] using
        (forceDistance_total_add 0 (0 : VelocityField)
          (periodize (InsertionFamily.force ν f v 0 T θ η ε)))
    _ < (⊤ : ℝ≥0∞) := hdist

/-- The genuine periodized insertion force has finite first-order distance
from the zero force for all sufficiently small positive scales. -/
theorem eventually_forceDistance_lt_top_actual_insertion_periodized_one
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      forceDistance 1
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) 0 <
          (⊤ : ℝ≥0∞) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hb⟩ :=
    eventually_actual_insertion_vector_periodized_endpoint_bound
      ν hf hfc hv T hθ hη hθc hηc (s := (1 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [hb] with ε hε
  have hfin := insertion_endpoint_rhs_one_lt_top
    (ε := ε) (C₀ := C₀) (C₁ := C₁) hC₁
  have hdist :
      eLpNorm (fun t => periodicVectorSobolevNorm 1
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume <
        (⊤ : ℝ≥0∞) := hε.trans_lt hfin
  calc
    forceDistance 1
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) 0 =
        eLpNorm (fun t => periodicVectorSobolevNorm 1
          (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume := by
      simpa only [Pi.zero_apply, zero_add] using
        (forceDistance_total_add 1 (0 : VelocityField)
          (periodize (InsertionFamily.force ν f v 0 T θ η ε)))
    _ < (⊤ : ℝ≥0∞) := hdist

/-- The same endpoint finiteness after exposing the actual periodic-force
constructor used by the insertion fiber. -/
theorem eventually_forceDistance_lt_top_actual_insertion_zero
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      forceDistance 0
        (PeriodicInsertion.force (InsertionFamily.force ν f v 0 T θ η ε)) 0 <
          (⊤ : ℝ≥0∞) := by
  simpa only [PeriodicInsertion.force] using
    eventually_forceDistance_lt_top_actual_insertion_periodized_zero
      ν hf hfc hv T hθ hη hθc hηc

theorem eventually_forceDistance_lt_top_actual_insertion_one
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      forceDistance 1
        (PeriodicInsertion.force (InsertionFamily.force ν f v 0 T θ η ε)) 0 <
          (⊤ : ℝ≥0∞) := by
  simpa only [PeriodicInsertion.force] using
    eventually_forceDistance_lt_top_actual_insertion_periodized_one
      ν hf hfc hv T hθ hη hθc hηc

end NSFormalization.Paper1.PeriodicInsertionFiniteEndpoints
