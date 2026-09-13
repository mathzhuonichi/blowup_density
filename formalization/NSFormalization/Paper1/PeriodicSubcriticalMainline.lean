import NSFormalization.Paper1.PeriodicForceTimeInterpolation
import NSFormalization.Paper1.PeriodicScalarForceEndpoints
import NSFormalization.Paper1.PeriodicEndpointTimeBridge
import NSFormalization.Paper1.PeriodicInsertionPositiveConvergence

/-!
# Short Paper 1 subcritical force route

This is the compact interface for the subcritical force estimate.  The proof
route is deliberately endpoint-first: the actual periodic order-zero and
order-one endpoint identities are combined by Fourier interpolation in time,
and the insertion endpoint rates then give `ε^(1/2-s)`.  The nonpositive-order
branch is handled by monotonicity.  Consequently downstream Paper 1 arguments
need only invoke this theorem; they do not need to repeat a fractional
localization or Gagliardo decomposition.

The theorem is still a subcritical force statement.  It does not assert the
uniform critical `H^(1/2) -> L^3` embedding, arbitrary-data local existence,
or the full density theorem.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicSubcriticalMainline

open Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceConvergence
open NavierStokes.PeriodicIntegration
open NSFormalization.Paper1.PeriodicInsertionPositiveConvergence
open scoped ContDiff ENNReal Topology


/-- Explicit endpoint-interpolation rate exposed for downstream scaling
arguments.  The exponent `1/2 - s` is positive under the stated
subcritical hypothesis. -/
theorem insertion_force_subcritical_power_mainline
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1 / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      eLpNorm (fun t => periodicVectorSobolevNorm s
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume ≤
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2 - s)) * C := by
  exact insertion_force_periodic_L1_power_bound ν hf hfc hv T hθ hη hθc hηc
    hs0 (le_of_lt (by linarith : s < 1))

/-- Single-call subcritical convergence interface for the complete periodic
insertion force.  All analytic work is discharged by the endpoint/time bridge
and the nonpositive-order monotonicity adapter. -/
theorem insertion_force_subcritical_mainline
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs : s < 1 / 2) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => periodicVectorSobolevNorm s
      (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  exact insertion_force_periodic_L1_tendsto_zero ν hf hfc hv T hθ hη hθc hηc hs

end NSFormalization.Paper1.PeriodicSubcriticalMainline
