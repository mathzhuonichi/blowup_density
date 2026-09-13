import NSFormalization.Paper1.PeriodicForceEndpointScaling

/-!
# Instantiating periodic endpoint rates for a concentrating family

Eventual fixed-cube support and whole-space endpoint bounds are sufficient to
produce the periodized subcritical bound. The zero-order periodization bound is
derived from the exact Parseval identity at each scale, rather than supplied as
an additional localization hypothesis.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicEndpointInstantiation

open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper3
open NSFormalization.Paper1.PeriodicForceEndpointScaling
open NSFormalization.Paper1.PeriodicEndpointTimeBridge
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.PeriodicScalarForceEndpoints
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal FourierTransform

theorem eventually_periodized_scalar_L1Hs_rate_of_whole_endpoint_bounds
    {F : ℝ → SpaceTime → ℂ} {A₀ A₁ α β s : ℝ}
    (hF : ∀ ε, ContDiff ℝ ∞ (F ε))
    (hc : ∀ ε, HasCompactSupport (F ε))
    (hsupp :
      Filter.Eventually
        (fun ε : ℝ => SupportedInCube (1 / 4) (F ε))
        (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hzero_whole : ∀ ε > 0, eLpNorm (fun t =>
      fourierSobolevNorm 0 (fun x => F ε (t, x))) 1 volume ≤
      ENNReal.ofReal (A₀ * ε ^ α))
    (hone_whole : ∀ ε > 0, eLpNorm (fun t =>
      fourierSobolevNorm 1 (fun x => F ε (t, x))) 1 volume ≤
      ENNReal.ofReal (A₁ * ε ^ β))
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Filter.Eventually
      (fun ε : ℝ =>
        eLpNorm (fun t => periodicSobolevNorm s
          (fun x => periodize (F ε) (t, x))) 1 volume ≤
        (ENNReal.ofReal (A₀ * ε ^ α)) ^ (1 - s) *
          (ENNReal.ofReal (2 * Real.pi) *
            ENNReal.ofReal (A₁ * ε ^ β)) ^ s)
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  filter_upwards [self_mem_nhdsWithin, hsupp] with ε hε hS
  apply periodic_scalar_L1Hs_le_of_endpoint_bounds hS (by norm_num)
    (hF ε) (hc ε) hs0 hs1
    (A0 := ENNReal.ofReal (A₀ * ε ^ α))
    (A1 := ENNReal.ofReal (A₁ * ε ^ β))
  · exact (continuous_periodized_zero_time hS (by norm_num) (hF ε) (hc ε)).aemeasurable
  · have heq : eLpNorm (fun t => periodicSobolevNorm 0
        (fun x => periodize (F ε) (t, x))) 1 volume =
        eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => F ε (t, x))) 1 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [] with t
      have hpoint : periodicSobolevNorm 0
          (fun x => periodize (F ε) (t, x)) =
          fourierSobolevNorm 0 (fun x => F ε (t, x)) := by
        let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport
          (fun x => F ε (t, x))
          ((hF ε).comp (contDiff_const.prodMk contDiff_id))
          (compact_spatial_slice (hc ε) t)
        have hi : Integrable (fun x : Space => ‖F ε (t, x)‖ ^ 2) :=
          (φ.memLp 2 volume).integrable_norm_pow (by norm_num)
        have hcont : Continuous (fun x : Space => periodize (F ε) (t, x)) :=
          ((contDiff_periodize hS (hF ε)).comp
            (contDiff_const.prodMk contDiff_id)).continuous
        unfold periodicSobolevNorm Source.fourierSobolevNorm
        congr 1
        rw [periodicSobolevSq_zero hcont,
          cubeIntegral_periodize_norm_sq hS (by norm_num) hi,
          Source.fourierSobolevSq]
        simpa [φ, Real.rpow_zero, SchwartzMap.fourier_coe] using
          (SchwartzMap.integral_norm_sq_fourier φ).symm
      exact hpoint
    exact heq.le.trans (hzero_whole ε hε)
  · exact (continuous_periodized_one_time hS (by norm_num) (hF ε) (hc ε)).aemeasurable
  · exact hone_whole ε hε

end NSFormalization.Paper1.PeriodicEndpointInstantiation
