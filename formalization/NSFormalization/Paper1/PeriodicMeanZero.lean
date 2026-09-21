import NSFormalization.Paper1.PeriodicFourierDerivative

/-! Mean-zero consequences of the periodic Fourier coefficient formula.

Contract: identify the zero Fourier coefficient with the cube integral, and
characterize vanishing mean by vanishing of that coefficient. No embedding
claim is made here.
-/
noncomputable section
namespace NSFormalization.Paper1
open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal BigOperators

/-- The zero Fourier coefficient is the integral over the periodic cube. -/
theorem periodicFourierCoeff_zero_eq_cubeIntegral (f : Space → ℂ) :
    periodicFourierCoeff f 0 = cubeIntegral f := by
  rw [periodicFourierCoeff_eq_cube]
  simp [periodicCharacter, periodicPhase]

/-- The zero Fourier coefficient vanishes exactly when the cube mean vanishes. -/
theorem periodicFourierCoeff_zero_eq_zero_iff (f : Space → ℂ) :
    periodicFourierCoeff f 0 = 0 ↔ cubeIntegral f = 0 := by
  rw [periodicFourierCoeff_zero_eq_cubeIntegral]

end NSFormalization.Paper1
