import NSFormalization.Paper1.CorrectionVectorNorms

/-!
# Whole-space endpoint rates for the localized correction force

The existing scalar correction estimates already prove the two endpoint
rates needed by the Paper 1 interpolation bridge. This file only packages
those results: at `q = 1`, the correction has H⁰ rate `ε^(3/2)` and H¹ rate
`ε^(1/2)`. Periodization and its support adapter remain separate obligations.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicCorrectionEndpointRates

open Set MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.CorrectionForceNorms
open NSFormalization.Paper1.CorrectionProfile
open scoped ContDiff ENNReal FourierTransform

/-- Scalar whole-space H⁰/H¹ endpoint rates for the physical background
correction. The constants are finite profile norms supplied by the existing
`CorrectionPositiveNorms` estimates. -/
theorem correction_scalar_whole_endpoint_rates
    (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3) :
    ∃ C₀ C₁ : ℝ≥0∞, C₀ < (⊤ : ℝ≥0∞) ∧ C₁ < (⊤ : ℝ≥0∞) ∧
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        eLpNorm (fun t => Source.fourierSobolevNorm 0
          (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) 1 volume ≤
            ENNReal.ofReal (ε ^ ((3 : ℝ) / 2)) * C₀ ∧
        eLpNorm (fun t => Source.fourierSobolevNorm 1
          (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) 1 volume ≤
            ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₁ := by
  obtain ⟨C₀, hC₀, h0⟩ := scalarPhysicalForce_uniform_positive_time ν hv x₀ T
    hθ hη hθc hηc i (s := 0) (by norm_num) (by norm_num) 1
  obtain ⟨C₁, hC₁, h1⟩ := scalarPhysicalForce_uniform_positive_time ν hv x₀ T
    hθ hη hθc hηc i (s := 1) (by norm_num) (by norm_num) 1
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro ε hε
  constructor
  · convert h0 ε hε using 1 <;> norm_num
  · convert h1 ε hε using 1 <;> norm_num

/-- Vector whole-space endpoint rates obtained by the existing finite
three-component assembly theorem. This is the form consumed by vector
periodic adapters once a support-in-one-cube statement is supplied. -/
theorem correction_vector_whole_endpoint_rates
    (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∃ C₀ C₁ : ℝ≥0∞, C₀ < (⊤ : ℝ≥0∞) ∧ C₁ < (⊤ : ℝ≥0∞) ∧
      ∀ ε ∈ Ioc (0 : ℝ) 1,
        eLpNorm (vectorFourierSobolevNorm 0
          (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))) 1 volume ≤
            ENNReal.ofReal (ε ^ ((3 : ℝ) / 2)) * C₀ ∧
        eLpNorm (vectorFourierSobolevNorm 1
          (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))) 1 volume ≤
            ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₁ := by
  obtain ⟨C₀, hC₀, h0⟩ := vectorPhysicalForce_uniform_positive_time ν hv x₀ T
    hθ hη hθc hηc (s := 0) (by norm_num) (by norm_num) 1 (by norm_num)
  obtain ⟨C₁, hC₁, h1⟩ := vectorPhysicalForce_uniform_positive_time ν hv x₀ T
    hθ hη hθc hηc (s := 1) (by norm_num) (by norm_num) 1 (by norm_num)
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro ε hε
  constructor
  · convert h0 ε hε using 1 <;> norm_num
  · convert h1 ε hε using 1 <;> norm_num

end NSFormalization.Paper1.PeriodicCorrectionEndpointRates
