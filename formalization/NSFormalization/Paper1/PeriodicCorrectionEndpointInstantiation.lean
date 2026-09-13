import NSFormalization.Paper1.PeriodicCorrectionEndpointRates
import NSFormalization.Paper1.PeriodicInsertionSupport
import NSFormalization.Paper1.PeriodicForceEndpointScaling

/-!
# Periodized endpoint product for the background correction

The whole-space correction rates are combined with the eventual fixed-cube
support of the actual correction force.  The result keeps the finite endpoint
profile constants explicit; it is a positive-order endpoint adapter and does
not assert the missing support-independent fractional localization theorem.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicCorrectionEndpointInstantiation

open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.CorrectionForceNorms
open NSFormalization.Paper1.PeriodicCorrectionEndpointRates
open NSFormalization.Paper1.PeriodicForceEndpointScaling
open NSFormalization.Paper1.CorrectionProfile
open NSFormalization.Paper1.CorrectionForceProfile
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal FourierTransform

/-- Eventual scalar periodized endpoint product for the actual background
correction force.  The endpoint constants are the finite whole-space profile
norms supplied by `correction_scalar_whole_endpoint_rates`. -/
theorem eventually_correction_coordinate_periodized_endpoint_product
    (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    (hcenter : ‖x₀‖ < 1 / 4)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ C₀ C₁ : ℝ≥0∞, C₀ < (⊤ : ℝ≥0∞) ∧ C₁ < (⊤ : ℝ≥0∞) ∧
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        eLpNorm (fun t => periodicSobolevNorm s
          (fun x => periodize
            (fun z => scalarPhysicalForce ν v x₀ T θ η i ε z) (t, x))) 1 volume ≤
          (ENNReal.ofReal (ε ^ ((3 : ℝ) / 2)) * C₀) ^ (1 - s) *
            (ENNReal.ofReal (2 * Real.pi) *
              (ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * C₁)) ^ s := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hrates⟩ :=
    correction_scalar_whole_endpoint_rates ν hv x₀ T hθ hη hθc hηc i
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  have hsupp : Filter.Eventually (fun ε : ℝ =>
      SupportedInCube (1 / 4)
        (scalarPhysicalForce ν v x₀ T θ η i ε))
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    filter_upwards [eventually_supportedInQuarterCube_physicalCorrectionForce_center
      ν v x₀ T η hθc hcenter] with ε hε
    change SupportedInCube (1 / 4) (fun z =>
      (correctionForce ν v (physicalCorrection v x₀ T θ η ε) z i : ℂ))
    exact supported_comp hε (fun w : Space => (w i : ℂ)) (by simp)
  have hrange : Filter.Eventually (fun ε : ℝ => ε ∈ Ioc (0 : ℝ) 1)
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with ε hε hε1
    exact ⟨hε, hε1⟩
  filter_upwards [hsupp, hrange] with ε hS hε
  have hsmooth : ContDiff ℝ ∞
      (scalarPhysicalForce ν v x₀ T θ η i ε) := by
    change ContDiff ℝ ∞
      (Source.coordinateForce
        (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) i)
    exact Source.coordinateForce_smooth
      (physicalForce_smooth ν hv x₀ T ε hθ hη) i
  have hcompact : HasCompactSupport
      (scalarPhysicalForce ν v x₀ T θ η i ε) := by
    change HasCompactSupport
      (Source.coordinateForce
        (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) i)
    exact Source.coordinateForce_compact
      (physicalForce_compact ν v x₀ T ε (ne_of_gt hε.1) hθc hηc) i
  have hbase := periodized_scalar_L1Hs_le_endpoint_product hS (by norm_num)
    hsmooth hcompact hs0 hs1
  have hrate := hrates ε hε
  apply hbase.trans
  gcongr
  · exact hrate.1
  · exact hrate.2

end NSFormalization.Paper1.PeriodicCorrectionEndpointInstantiation
