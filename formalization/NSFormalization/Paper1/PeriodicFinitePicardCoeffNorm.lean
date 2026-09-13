import NSFormalization.Paper1.PeriodicFinitePicardCoeff

noncomputable section
namespace NSFormalization.Paper1.PeriodicFinitePicardCoeffNorm

open Set MeasureTheory
open NSFormalization.Paper1.PeriodicPicardBilinear
open NSFormalization.Paper1.PeriodicHeatMultiplier
open NSFormalization.Paper1.PeriodicFinitePicardCoeff

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

/-- Pointwise coefficient norm bound for the finite-frequency Picard map.
The bound is intentionally expressed with the norm of the interval integrand:
it uses only the triangle inequality and the interval-integral norm estimate.
The explicit integrability hypothesis records the analytic input needed when
this bound is later combined with integral algebra. -/
theorem norm_picardCoeff_le
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (ht : 0 ≤ t)
    (n : PeriodicFrequency) (u₀ : FiniteFourier)
    (u f : ℝ → FiniteFourier)
    (hInt : IntervalIntegrable
      (fun τ : ℝ =>
        (heatSymbol ν (max (t - τ) 0) n : ℂ) *
          (convolutionCoeff (u τ) (u τ) n + f τ n))
      volume 0 t) :
    ‖picardCoeff ν hν t n u₀ u f‖ ≤
      ‖(heatSymbol ν t n : ℂ) * u₀ n‖ +
        ∫ τ in (0 : ℝ)..t,
          ‖(heatSymbol ν (max (t - τ) 0) n : ℂ) *
            (convolutionCoeff (u τ) (u τ) n + f τ n)‖ := by
  unfold picardCoeff
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := fun τ : ℝ =>
      (heatSymbol ν (max (t - τ) 0) n : ℂ) *
        (convolutionCoeff (u τ) (u τ) n + f τ n)) (a := (0 : ℝ)) (b := t) ht
  apply (norm_add_le _ _).trans
  simpa only [add_comm] using (add_le_add_left hnorm ‖(heatSymbol ν t n : ℂ) * u₀ n‖)

/-- For zero initial data and zero trajectory, the coefficient norm is bounded
by the norm of the forcing Duhamel integrand. This is the forcing-only
specialization of `norm_picardCoeff_le`; it carries an explicit integrability
contract but makes no claim about nonlinear estimates or contraction. -/
theorem norm_picardCoeff_zero_initial_zero_trajectory_le_forcing
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (ht : 0 ≤ t)
    (n : PeriodicFrequency) (f : ℝ → FiniteFourier)
    (hInt : IntervalIntegrable
      (fun τ : ℝ =>
        (heatSymbol ν (max (t - τ) 0) n : ℂ) * f τ n)
      volume 0 t) :
    ‖picardCoeff ν hν t n (0 : FiniteFourier) (fun _ => 0) f‖ ≤
      ∫ τ in (0 : ℝ)..t,
        ‖(heatSymbol ν (max (t - τ) 0) n : ℂ) * f τ n‖ := by
  rw [picardCoeff_zero_initial_zero_trajectory]
  exact intervalIntegral.norm_integral_le_integral_norm ht


/-- The forcing-only bound with the heat multiplier factored out of the
coefficient norm. This is an exact scalar norm rewrite and does not assert
any time-integrability or contraction estimate beyond the displayed contract. -/
theorem norm_picardCoeff_zero_initial_zero_trajectory_le_forcing_heat_factor
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (ht : 0 ≤ t)
    (n : PeriodicFrequency) (f : ℝ → FiniteFourier)
    (hInt : IntervalIntegrable
      (fun τ : ℝ =>
        (heatSymbol ν (max (t - τ) 0) n : ℂ) * f τ n)
      volume 0 t) :
    ‖picardCoeff ν hν t n (0 : FiniteFourier) (fun _ => 0) f‖ ≤
      ∫ τ in (0 : ℝ)..t,
        heatSymbol ν (max (t - τ) 0) n * ‖f τ n‖ := by
  calc
    ‖picardCoeff ν hν t n (0 : FiniteFourier) (fun _ => 0) f‖ ≤
        ∫ τ in (0 : ℝ)..t,
          ‖(heatSymbol ν (max (t - τ) 0) n : ℂ) * f τ n‖ :=
      norm_picardCoeff_zero_initial_zero_trajectory_le_forcing ν hν t ht n f hInt
    _ = ∫ τ in (0 : ℝ)..t,
          heatSymbol ν (max (t - τ) 0) n * ‖f τ n‖ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with τ hτ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (heatSymbol_nonneg ν (max (t - τ) 0) n)]

end NSFormalization.Paper1.PeriodicFinitePicardCoeffNorm
