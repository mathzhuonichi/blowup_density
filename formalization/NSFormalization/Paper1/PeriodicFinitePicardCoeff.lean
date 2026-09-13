import NSFormalization.Paper1.PeriodicPicardBilinear
import NSFormalization.Paper1.PeriodicHeatMultiplier

noncomputable section
namespace NSFormalization.Paper1.PeriodicFinitePicardCoeff

open Set MeasureTheory
open scoped BigOperators
open NSFormalization.Paper1.PeriodicHeatMultiplier
open NSFormalization.Paper1.PeriodicPicardBilinear

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

/-- One output-frequency coefficient of the finite-support Picard map.
This is a coefficient-level algebraic map: no claim is made that it is a
completed Hilbert-valued flow or a classical PDE solution. -/
def picardCoeff (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (n : PeriodicFrequency)
    (u₀ : FiniteFourier) (u f : ℝ → FiniteFourier) : ℂ :=
  (heatSymbol ν t n : ℂ) * u₀ n +
    ∫ τ in (0 : ℝ)..t,
      (heatSymbol ν (max (t - τ) 0) n : ℂ) *
        (convolutionCoeff (u τ) (u τ) n + f τ n)

/-- The zero initial/trajectory/forcing coefficient is zero. -/
@[simp] theorem picardCoeff_zero
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (n : PeriodicFrequency) :
    picardCoeff ν hν t n (0 : FiniteFourier) (fun _ => 0) (fun _ => 0) = 0 := by
  unfold picardCoeff
  simp [convolutionCoeff]

/-- Heat-only reduction when both the trajectory and forcing vanish. -/
theorem picardCoeff_zero_inputs
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (n : PeriodicFrequency)
    (u₀ : FiniteFourier) :
    picardCoeff ν hν t n u₀ (fun _ => 0) (fun _ => 0) =
      (heatSymbol ν t n : ℂ) * u₀ n := by
  unfold picardCoeff
  simp [convolutionCoeff]


/-- With zero initial coefficient and zero trajectory, `picardCoeff` is exactly
 the linear forced Duhamel contribution.  This is an algebraic identity; no
 integrability or PDE regularity is asserted. -/
theorem picardCoeff_zero_initial_zero_trajectory
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (n : PeriodicFrequency)
    (f : ℝ → FiniteFourier) :
    picardCoeff ν hν t n (0 : FiniteFourier) (fun _ => 0) f =
      ∫ τ in (0 : ℝ)..t,
        (heatSymbol ν (max (t - τ) 0) n : ℂ) * f τ n := by
  unfold picardCoeff
  simp [convolutionCoeff]

/-- The zero forcing specialization removes the Duhamel term for any fixed
 trajectory.  The nonlinear contribution remains, so this is not a claim of
 linearity in the trajectory argument. -/
theorem picardCoeff_zero_forcing
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (n : PeriodicFrequency)
    (u₀ : FiniteFourier) (u : ℝ → FiniteFourier) :
    picardCoeff ν hν t n u₀ u (fun _ => 0) =
      (heatSymbol ν t n : ℂ) * u₀ n +
        ∫ τ in (0 : ℝ)..t,
          (heatSymbol ν (max (t - τ) 0) n : ℂ) * convolutionCoeff (u τ) (u τ) n := by
  unfold picardCoeff
  simp


/-- For zero initial data and zero trajectory, the forcing contribution is
additive.  The integrability hypotheses are exactly those needed to split the
interval integral; no linearity in the nonlinear trajectory is asserted. -/
theorem picardCoeff_zero_initial_zero_trajectory_forcing_add
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (n : PeriodicFrequency)
    (f g : ℝ → FiniteFourier)
    (hf : IntervalIntegrable
      (fun τ : ℝ => (heatSymbol ν (max (t - τ) 0) n : ℂ) * f τ n)
      volume 0 t)
    (hg : IntervalIntegrable
      (fun τ : ℝ => (heatSymbol ν (max (t - τ) 0) n : ℂ) * g τ n)
      volume 0 t) :
    picardCoeff ν hν t n (0 : FiniteFourier) (fun _ => 0) (fun τ => f τ + g τ) =
      picardCoeff ν hν t n (0 : FiniteFourier) (fun _ => 0) f +
        picardCoeff ν hν t n (0 : FiniteFourier) (fun _ => 0) g := by
  rw [picardCoeff_zero_initial_zero_trajectory,
    picardCoeff_zero_initial_zero_trajectory,
    picardCoeff_zero_initial_zero_trajectory]
  rw [← intervalIntegral.integral_add hf hg]
  congr 1
  funext τ
  change (heatSymbol ν (max (t - τ) 0) n : ℂ) * ((f τ) n + (g τ) n) = _
  rw [mul_add]

end NSFormalization.Paper1.PeriodicFinitePicardCoeff
