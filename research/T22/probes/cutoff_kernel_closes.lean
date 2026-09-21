import NSFormalization.Section3.T22.CutoffKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
Probe for T22 U-A2 (`Section3/T22/CutoffKernel.lean`): a concrete smooth compact
cutoff built from `ContDiffBump` closes the weighted-`L¹` integrability of its
Fourier kernel at `s = 1/2` and `s = -2`, in both the angular and Mathlib
spellings, plus the `ENNReal` finiteness form.
-/

noncomputable section
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Source (angularFourier)
open scoped ContDiff SchwartzMap
open NSFormalization.Section3.T22

/-- A concrete radial bump on ℝ³: `1` on the unit ball, supported in the ball of radius `2`. -/
def probeBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, by norm_num⟩

def probeChi : Space → ℝ := (probeBump : Space → ℝ)

theorem probeChi_contDiff : ContDiff ℝ ∞ probeChi := probeBump.contDiff

theorem probeChi_hasCompactSupport : HasCompactSupport probeChi := probeBump.hasCompactSupport

-- Angular (datum-layer) version at s = 1/2 and s = -2.
example : Integrable (fun ζ : Space =>
    (1 + ‖ζ‖ ^ 2) ^ (|(1/2 : ℝ)| / 2) * ‖angularFourier (fun x => (probeChi x : ℂ)) ζ‖) :=
  integrable_weighted_fourier_cutoff probeChi_contDiff probeChi_hasCompactSupport (1/2)

example : Integrable (fun ζ : Space =>
    (1 + ‖ζ‖ ^ 2) ^ (|(-2 : ℝ)| / 2) * ‖angularFourier (fun x => (probeChi x : ℂ)) ζ‖) :=
  integrable_weighted_fourier_cutoff probeChi_contDiff probeChi_hasCompactSupport (-2)

-- Mathlib (cycles) version at s = 1/2 and s = -2.
example : Integrable (fun ζ : Space =>
    (1 + ‖ζ‖ ^ 2) ^ (|(1/2 : ℝ)| / 2) * ‖𝓕 (fun x => (probeChi x : ℂ)) ζ‖) :=
  integrable_weighted_fourier_cutoff_mathlib probeChi_contDiff probeChi_hasCompactSupport (1/2)

example : Integrable (fun ζ : Space =>
    (1 + ‖ζ‖ ^ 2) ^ (|(-2 : ℝ)| / 2) * ‖𝓕 (fun x => (probeChi x : ℂ)) ζ‖) :=
  integrable_weighted_fourier_cutoff_mathlib probeChi_contDiff probeChi_hasCompactSupport (-2)

-- ENNReal finiteness form at s = 1/2 and s = -2.
example : (∫⁻ ζ : Space, ENNReal.ofReal
    ((1 + ‖ζ‖ ^ 2) ^ (|(1/2 : ℝ)| / 2) * ‖angularFourier (fun x => (probeChi x : ℂ)) ζ‖)) ≠ ⊤ :=
  lintegral_weighted_fourier_cutoff_ne_top probeChi_contDiff probeChi_hasCompactSupport (1/2)

example : (∫⁻ ζ : Space, ENNReal.ofReal
    ((1 + ‖ζ‖ ^ 2) ^ (|(-2 : ℝ)| / 2) * ‖angularFourier (fun x => (probeChi x : ℂ)) ζ‖)) ≠ ⊤ :=
  lintegral_weighted_fourier_cutoff_ne_top probeChi_contDiff probeChi_hasCompactSupport (-2)
