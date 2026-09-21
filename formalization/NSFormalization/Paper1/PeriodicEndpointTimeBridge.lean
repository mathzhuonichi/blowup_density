import NSFormalization.Paper1.PeriodicScalarForceEndpoints
import NSFormalization.Paper1.PeriodicForceTimeInterpolation

/-!
# Conditional endpoint-to-time bridge for Paper 1 forces

This file combines the proved order-one periodization endpoint with the proved
spectral time interpolation.  The zero-order time profile and its measurability
are kept as explicit inputs: supplying those data is separate from the
critical fractional localization problem.
-/

noncomputable section
namespace NSFormalization.Paper1
namespace PeriodicEndpointTimeBridge

open Set Filter MeasureTheory NavierStokes.ProblemStatement
open NavierStokesR3.HarmonicTestFunctionals
open NSFormalization.Source
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open PeriodicScalarForceEndpoints PeriodicForceTimeInterpolation
open NSFormalization.Source
open scoped ContDiff ENNReal Topology FourierTransform

/-- For one compactly supported scalar spacetime force, endpoint bounds imply
an explicit periodic `L¹_t H^s_x` bound.  The order-one endpoint contributes
exactly the proved factor `2 * pi`; the zero-order endpoint is intentionally
an explicit premise. -/
theorem periodic_scalar_L1Hs_le_of_endpoint_bounds
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {μ : Measure ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {A0 A1 : ℝ≥0∞}
    (hzero_meas : AEMeasurable
      (fun t : ℝ => periodicSobolevNorm 0 (fun x => periodize F (t, x))) μ)
    (hzero_bound : eLpNorm
      (fun t : ℝ => periodicSobolevNorm 0 (fun x => periodize F (t, x))) 1 μ ≤ A0)
    (hone_meas : AEMeasurable
      (fun t : ℝ => periodicSobolevNorm 1 (fun x => periodize F (t, x))) μ)
    (hone_whole : eLpNorm
      (fun t => fourierSobolevNorm 1 (fun x => F (t, x))) 1 μ ≤ A1) :
    eLpNorm
      (fun t => periodicSobolevNorm s (fun x => periodize F (t, x))) 1 μ ≤
      A0 ^ (1 - s) *
        (ENNReal.ofReal (2 * Real.pi) * A1) ^ s := by
  have hF1 : ∀ t : ℝ, ContDiff ℝ 1
      (fun x : Space => periodize F (t, x)) := by
    intro t
    exact ((contDiff_periodize hS hF).comp
      (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  have hp : ∀ t : ℝ, UnitPeriods
      (fun x : Space => periodize F (t, x)) := by
    intro t x i
    exact unitSpatialPeriodsOn_periodize F univ t (mem_univ _) x i
  have hpoint := periodic_force_L1_interpolation
    (μ := μ) hF1 hp hzero_meas hone_meas hs0 hs1
  have hone_periodic : eLpNorm
      (fun t => periodicSobolevNorm 1 (fun x => periodize F (t, x))) 1 μ ≤
      ENNReal.ofReal (2 * Real.pi) * A1 := by
    exact (eLpNorm_periodized_one_le hS hr hF hc 1 μ).trans
      (by simpa [mul_comm] using
        (mul_le_mul_left hone_whole (ENNReal.ofReal (2 * Real.pi) : ℝ≥0∞)))
  have hpow :
      eLpNorm (fun t => periodicSobolevNorm 1 (fun x => periodize F (t, x))) 1 μ ^ s ≤
        (ENNReal.ofReal (2 * Real.pi) * A1) ^ s := by
    exact ENNReal.rpow_le_rpow hone_periodic hs0
  calc
    eLpNorm (fun t => periodicSobolevNorm s
      (fun x => periodize F (t, x))) 1 μ ≤
        eLpNorm (fun t => periodicSobolevNorm 0
          (fun x => periodize F (t, x))) 1 μ ^ (1 - s) *
          eLpNorm (fun t => periodicSobolevNorm 1
            (fun x => periodize F (t, x))) 1 μ ^ s := hpoint
    _ ≤ A0 ^ (1 - s) * (ENNReal.ofReal (2 * Real.pi) * A1) ^ s := by
      gcongr

end PeriodicEndpointTimeBridge
end NSFormalization.Paper1
