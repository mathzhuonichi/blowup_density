import NSFormalization.Paper1.PeriodicEndpointTimeBridge
import NSFormalization.Paper1.PeriodicScalarForceEndpoints
import NSFormalization.Paper3.CompactFourierTime

/-!
# Endpoint scaling wrapper for periodized scalar forces

This module instantiates the endpoint-to-time bridge with the actual endpoint
profiles.  It retains the order-one factor `2*pi` and makes no fractional
localization or critical embedding claim.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicForceEndpointScaling

open Set MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open NSFormalization.Source NSFormalization.Paper3
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.PeriodicEndpointTimeBridge
open NSFormalization.Paper1.PeriodicScalarForceEndpoints
open scoped ContDiff ENNReal FourierTransform

theorem periodized_scalar_L1Hs_le_endpoint_product
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    eLpNorm (fun t => periodicSobolevNorm s
      (fun x => periodize F (t, x))) 1 volume ≤
      eLpNorm (fun t => fourierSobolevNorm 0 (fun x => F (t, x))) 1 volume ^ (1 - s) *
      (ENNReal.ofReal (2 * Real.pi) *
        eLpNorm (fun t => fourierSobolevNorm 1 (fun x => F (t, x))) 1 volume) ^ s := by
  apply periodic_scalar_L1Hs_le_of_endpoint_bounds (μ := (volume : Measure ℝ))
    hS hr hF hc hs0 hs1
    (A0 := eLpNorm (fun t => fourierSobolevNorm 0 (fun x => F (t, x))) 1 volume)
    (A1 := eLpNorm (fun t => fourierSobolevNorm 1 (fun x => F (t, x))) 1 volume)
  · exact (continuous_periodized_zero_time hS hr hF hc).aemeasurable
  · apply le_of_eq
    apply eLpNorm_congr_ae
    filter_upwards [] with t
    have hpoint : periodicSobolevNorm 0
        (fun x => periodize F (t, x)) =
        fourierSobolevNorm 0 (fun x => F (t, x)) := by
      let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport
        (fun x => F (t, x))
        (hF.comp (contDiff_const.prodMk contDiff_id))
        (compact_spatial_slice hc t)
      have hi : Integrable (fun x : Space => ‖F (t, x)‖ ^ 2) :=
        (φ.memLp 2 volume).integrable_norm_pow (by norm_num)
      have hpTop : ContDiff ℝ ∞ (fun x : Space => periodize F (t, x)) :=
        (contDiff_periodize hS hF).comp (contDiff_const.prodMk contDiff_id)
      have hp : ContDiff ℝ 1 (fun x : Space => periodize F (t, x)) :=
        hpTop.of_le (by norm_num)
      unfold periodicSobolevNorm Source.fourierSobolevNorm
      congr 1
      rw [periodicSobolevSq_zero hp.continuous,
        cubeIntegral_periodize_norm_sq hS hr hi, Source.fourierSobolevSq]
      simpa [φ, Real.rpow_zero, SchwartzMap.fourier_coe] using
        (SchwartzMap.integral_norm_sq_fourier φ).symm
    exact hpoint
  · exact (continuous_periodized_one_time hS hr hF hc).aemeasurable
  · exact le_rfl

end NSFormalization.Paper1.PeriodicForceEndpointScaling
