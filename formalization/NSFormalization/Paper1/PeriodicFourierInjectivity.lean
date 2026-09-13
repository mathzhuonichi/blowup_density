import NSFormalization.Paper1.PeriodicH2Uniform
import NSFormalization.Paper1.PeriodicSmoothSobolev

/-! Fourier injectivity for smooth unit-periodic scalar fields. -/
noncomputable section
namespace NSFormalization.Paper1

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal BigOperators

theorem periodic_eq_zero_of_periodicSobolevSq_zero {s : ℝ}
    {f : Space → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriods f)
    (hzero : periodicSobolevSq s f = 0) : f = 0 := by
  have hc : Summable (periodicFourierCoeff f) :=
    summable_periodicFourierCoeff_of_h2_actual (hf.of_le (by norm_num)) hp
  funext x
  rw [← periodicFourier_tsum_eq hf.continuous hp hc x]
  simp [coeff_zero_of_periodicSobolevSq_zero hf hp hzero]

end NSFormalization.Paper1
