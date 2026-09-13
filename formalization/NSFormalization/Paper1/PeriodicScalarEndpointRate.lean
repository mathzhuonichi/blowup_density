import NSFormalization.Paper1.PeriodicEndpointTimeBridge

/-!
# Explicit endpoint-rate packaging for Paper 1

This wrapper turns the already proved endpoint-to-time interpolation theorem
into the exact epsilon-dependent estimate used by the packet and correction
families. The zero-order periodization estimate is an explicit input because
its component/vector assembly belongs to the separate endpoint module.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicScalarEndpointRate

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicEndpointTimeBridge
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal FourierTransform

/-- If a periodized scalar force has explicit endpoint rates, then its
subcritical `L¹_t H^s_x` norm has the interpolated epsilon rate. The theorem
keeps the endpoint powers in `ENNReal` form, which is valid also when an
endpoint constant is zero or an endpoint norm is infinite. -/
theorem periodized_scalar_L1Hs_rate_of_endpoint_bounds
    {r : ℝ} {F : ℝ → SpaceTime → ℂ} (hS : ∀ ε, SupportedInCube r (F ε))
    (hr : r < 1 / 2) (hF : ∀ ε, ContDiff ℝ ∞ (F ε))
    (hc : ∀ ε, HasCompactSupport (F ε))
    {A₀ A₁ α β s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hzero_meas : ∀ ε > 0, AEMeasurable (fun t =>
      periodicSobolevNorm 0 (fun x => periodize (F ε) (t, x))) volume)
    (hzero_bound : ∀ ε > 0,
      eLpNorm (fun t => periodicSobolevNorm 0
        (fun x => periodize (F ε) (t, x))) 1 volume ≤
        ENNReal.ofReal (A₀ * ε ^ α))
    (hone_meas : ∀ ε > 0, AEMeasurable (fun t =>
      periodicSobolevNorm 1 (fun x => periodize (F ε) (t, x))) volume)
    (hone_whole : ∀ ε > 0,
      eLpNorm (fun t => fourierSobolevNorm 1 (fun x => F ε (t, x))) 1 volume ≤
        ENNReal.ofReal (A₁ * ε ^ β)) :
    ∀ ε > 0,
      eLpNorm (fun t => periodicSobolevNorm s
        (fun x => periodize (F ε) (t, x))) 1 volume ≤
      (ENNReal.ofReal (A₀ * ε ^ α)) ^ (1 - s) *
        (ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (A₁ * ε ^ β)) ^ s := by
  intro ε hε
  apply periodic_scalar_L1Hs_le_of_endpoint_bounds
    (hS := hS ε) (hr := hr) (hF := hF ε) (hc := hc ε)
    (μ := (volume : Measure ℝ)) hs0 hs1
    (A0 := ENNReal.ofReal (A₀ * ε ^ α))
    (A1 := ENNReal.ofReal (A₁ * ε ^ β))
  · exact hzero_meas ε hε
  · exact hzero_bound ε hε
  · exact hone_meas ε hε
  · exact hone_whole ε hε


end NSFormalization.Paper1.PeriodicScalarEndpointRate
