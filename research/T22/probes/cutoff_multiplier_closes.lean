import NSFormalization.Section3.T22.CutoffMultiplier
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
Probe for T22 U-A3 (`Section3/T22/CutoffMultiplier.lean`).

Scope (see `research/T22/ATTEMPTS_UA3.md`): the verbatim `cutoffMultiplier`
field for a *general tempered* datum is NOT closed by this lane — the residual
is the datum-model plumbing (angular product↔convolution at the `L²` level,
real-subspace preservation, `smulLeftCLM` graph), not analysis.  What IS proved
is the analytic engine `eLpNorm_besselWeight_scalarConvolution_le` and its
cutoff specialization `eLpNorm_cutoff_multiplier_le`.  This probe exercises them
non-vacuously: a `ContDiffBump` cutoff and a genuinely nonzero input transform
whose Bessel-weighted profile is finite (`L²`), at `s = 1/2` and `s = -2`.
-/

noncomputable section
open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source (angularFourier)
open NavierStokes.R3ConvolutionYoung (scalarConvolution)
open scoped ContDiff ENNReal
open NSFormalization.Section3.T22

/-- A concrete radial bump on ℝ³: `1` on the unit ball, supported in the ball of radius `2`. -/
def probeBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, by norm_num⟩

def probeChi : Space → ℝ := (probeBump : Space → ℝ)

theorem probeChi_contDiff : ContDiff ℝ ∞ probeChi := probeBump.contDiff

theorem probeChi_hasCompactSupport : HasCompactSupport probeChi := probeBump.hasCompactSupport

/-- `besselW s · besselW (-s) = 1`: the Bessel weight and its inverse cancel. -/
theorem probe_besselW_mul_neg (s : ℝ) (η : Space) :
    besselW s η * besselW (-s) η = 1 := by
  unfold besselW
  rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero]

/-- A concrete **nonzero** `L²` datum-transform: the indicator of the unit ball. -/
def probeA : Space → ℂ := (Metric.ball (0 : Space) 1).indicator (fun _ => (1 : ℂ))

theorem probeA_memLp : MemLp probeA 2 volume :=
  memLp_indicator_const 2 measurableSet_ball (1 : ℂ) (Or.inr measure_ball_ne_top)

/-- The input transform whose Bessel-weighted profile is exactly `probeA`
(hence nonzero with finite `L²` norm). -/
def probeG (s : ℝ) : Space → ℂ := fun η => (besselW (-s) η : ℝ) • probeA η

theorem probeG_weighted_memLp (s : ℝ) :
    MemLp (fun η : Space => (besselW s η : ℝ) • probeG s η) 2 volume := by
  have hfun : (fun η : Space => (besselW s η : ℝ) • probeG s η) = probeA := by
    funext η
    show (besselW s η : ℝ) • ((besselW (-s) η : ℝ) • probeA η) = probeA η
    rw [smul_smul, probe_besselW_mul_neg s η, one_smul]
  rw [hfun]; exact probeA_memLp

-- The cutoff multiplier engine applies non-vacuously at `s = 1/2`.
example :
    eLpNorm (fun ξ : Space => (besselW (1 / 2 : ℝ) ξ : ℝ) •
        scalarConvolution (angularFourier (fun x => (probeChi x : ℂ))) (probeG (1 / 2)) ξ)
        2 volume ≤
      ENNReal.ofReal (cutoffMultiplierConst (1 / 2) probeChi) *
        eLpNorm (fun η : Space => (besselW (1 / 2 : ℝ) η : ℝ) • probeG (1 / 2) η) 2 volume :=
  eLpNorm_cutoff_multiplier_le probeChi_contDiff probeChi_hasCompactSupport (1 / 2)
    (probeG (1 / 2)) (probeG_weighted_memLp (1 / 2))

-- ... and at the negative order `s = -2`.
example :
    eLpNorm (fun ξ : Space => (besselW (-2 : ℝ) ξ : ℝ) •
        scalarConvolution (angularFourier (fun x => (probeChi x : ℂ))) (probeG (-2)) ξ)
        2 volume ≤
      ENNReal.ofReal (cutoffMultiplierConst (-2) probeChi) *
        eLpNorm (fun η : Space => (besselW (-2 : ℝ) η : ℝ) • probeG (-2) η) 2 volume :=
  eLpNorm_cutoff_multiplier_le probeChi_contDiff probeChi_hasCompactSupport (-2)
    (probeG (-2)) (probeG_weighted_memLp (-2))

-- The multiplier constant is a well-defined nonnegative real.
example : 0 ≤ cutoffMultiplierConst (1 / 2) probeChi :=
  cutoffMultiplierConst_nonneg _ _

-- The abstract engine also applies directly to the kernel `angularFourier χ_ℂ`.
example :
    eLpNorm (fun ξ : Space => (besselW (1 / 2 : ℝ) ξ : ℝ) •
        scalarConvolution (angularFourier (fun x => (probeChi x : ℂ))) (probeG (1 / 2)) ξ)
        2 volume ≤
      ENNReal.ofReal (peetreConst (1 / 2) *
          ∫ ζ : Space, besselW |(1 / 2 : ℝ)| ζ *
            ‖angularFourier (fun x => (probeChi x : ℂ)) ζ‖) *
        eLpNorm (fun η : Space => (besselW (1 / 2 : ℝ) η : ℝ) • probeG (1 / 2) η) 2 volume :=
  eLpNorm_besselWeight_scalarConvolution_le (1 / 2)
    (angularFourier (fun x => (probeChi x : ℂ))) (probeG (1 / 2))
    (by simpa only [besselW] using
      integrable_weighted_fourier_cutoff probeChi_contDiff probeChi_hasCompactSupport (1 / 2))
    (probeG_weighted_memLp (1 / 2))
