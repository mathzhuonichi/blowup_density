import NSFormalization.Paper1.PeriodicSobolev
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! Measurability of the actual periodic Fourier norm in time.
The coefficients are integrals over the fixed fundamental cube. Countable
summation and the square root preserve measurability. This proof does not
identify a periodic Fourier series with a whole-space Fourier transform.
-/
noncomputable section
namespace NSFormalization.Paper1
open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

theorem stronglyMeasurable_periodicFourierCoeff_time
    {F : SpaceTime → ℂ} (hF : Continuous F) (k : PeriodicFrequency) :
    StronglyMeasurable (fun t => periodicFourierCoeff (fun x => F (t, x)) k) := by
  have hc : Continuous (fun z : ℝ × Coords =>
      periodicCharacter (-k) (toSpace z.2) * F (z.1, toSpace z.2)) :=
    ((periodicCharacter_smooth (-k)).continuous.comp
      (toSpace.continuous.comp continuous_snd)).mul
      (hF.comp (continuous_fst.prodMk (toSpace.continuous.comp continuous_snd)))
  simp_rw [periodicFourierCoeff_eq_cube]
  exact hc.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure Coords).restrict cube)

/-- This assertion concerns measurability only. Analytic bounds elsewhere
separately establish summability, so divergent-series conventions are never
used to prove an estimate. -/
theorem stronglyMeasurable_periodicSobolevNorm_time
    (s : ℝ) {F : SpaceTime → ℂ} (hF : Continuous F) :
    StronglyMeasurable (fun t => periodicSobolevNorm s (fun x => F (t, x))) := by
  have hc := fun k => (stronglyMeasurable_periodicFourierCoeff_time hF k).measurable
  have hm : Measurable (fun t => periodicSobolevSq s (fun x => F (t, x))) := by
    apply Measurable.tsum
    intro k
    exact measurable_const.mul ((hc k).norm.pow_const 2)
  exact Real.continuous_sqrt.comp_stronglyMeasurable hm.stronglyMeasurable

/-- The unsquared Fourier energy is measurable as well.  Exporting this
  intermediate fact lets vector-valued periodic norms be assembled without
  introducing an unjustified square-root identity for potentially divergent
  series. -/
theorem stronglyMeasurable_periodicSobolevSq_time
    (s : ℝ) {F : SpaceTime → ℂ} (hF : Continuous F) :
    StronglyMeasurable (fun t => periodicSobolevSq s (fun x => F (t, x))) := by
  have hc := fun k => (stronglyMeasurable_periodicFourierCoeff_time hF k).measurable
  have hm : Measurable (fun t => periodicSobolevSq s (fun x => F (t, x))) := by
    apply Measurable.tsum
    intro k
    exact measurable_const.mul ((hc k).norm.pow_const 2)
  exact hm.stronglyMeasurable

end NSFormalization.Paper1
