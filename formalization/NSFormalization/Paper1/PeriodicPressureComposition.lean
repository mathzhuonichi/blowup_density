import NSFormalization.Paper1.PeriodicPressureSymbolOperator
import NSFormalization.Paper1.PeriodicHeatMultiplier

/-!
# Composition of periodic heat and pressure multipliers

These identities use the existing heat symbol on native integer frequencies.
They apply to arbitrary coefficient data and hence to every finite frequency
truncation. No physical reconstruction or smoothing assertion is assumed.
-/

noncomputable section

namespace NSFormalization.Paper1.PeriodicPressureComposition

open PeriodicPressureSymbol

/-- The existing periodic heat symbol acting on raw coefficient data. -/
def heatCoeffs (ν t : ℝ) (g : PeriodicFrequency → ℂ) : PeriodicFrequency → ℂ :=
  fun k => (PeriodicHeatMultiplier.heatSymbol ν t k : ℂ) * g k

/-- Identification with the complete Fourier Hilbert-space heat multiplier. -/
theorem heatCoeffs_eq_heat {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (g : PeriodicHeatMultiplier.FourierHilbert) :
    heatCoeffs ν t g = fun k => PeriodicHeatMultiplier.heat hν ht g k := rfl

@[simp] theorem heatCoeffs_zero_mode (ν t : ℝ) (g : PeriodicFrequency → ℂ) :
    heatCoeffs ν t g 0 = g 0 := by
  simp [heatCoeffs, PeriodicHeatMultiplier.heatSymbol,
    PeriodicHeatMultiplier.laplaceEigenvalue_eq]

/-- Pressure recovery commutes with heat evolution coefficient by coefficient. -/
theorem pressureOperator_heatCoeffs (ν t : ℝ) (g : PeriodicFrequency → ℂ) :
    pressureOperator (heatCoeffs ν t g) = heatCoeffs ν t (pressureOperator g) := by
  funext k
  simp only [pressureOperator_apply, pressureCoeff, heatCoeffs]
  ring_nf

/-- The Laplace and heat multipliers commute on raw coefficient data. -/
theorem laplaceOperator_heatCoeffs (ν t : ℝ) (g : PeriodicFrequency → ℂ) :
    laplaceOperator (heatCoeffs ν t g) = heatCoeffs ν t (laplaceOperator g) := by
  funext k
  simp only [laplaceOperator_apply, heatCoeffs]
  ring_nf

/-- Heat evolution commutes with arbitrary finite frequency truncation. -/
theorem truncateCoeffs_heatCoeffs (ν t : ℝ) (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) :
    truncateCoeffs S (heatCoeffs ν t g) = heatCoeffs ν t (truncateCoeffs S g) := by
  funext k
  by_cases hk : k ∈ S <;> simp [truncateCoeffs, heatCoeffs, hk]

/-- Finite frequency pressure recovery commutes with heat evolution. -/
theorem pressureOperatorOn_heatCoeffs (ν t : ℝ) (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) :
    pressureOperatorOn S (heatCoeffs ν t g) = heatCoeffs ν t (pressureOperatorOn S g) := by
  rw [← pressureOperator_truncateCoeffs, truncateCoeffs_heatCoeffs,
    pressureOperator_heatCoeffs, pressureOperator_truncateCoeffs]

/-- Heating a zero-mode-compatible source preserves its truncated Poisson
equation, including the zero mode. -/
theorem laplace_pressureOperatorOn_heatCoeffs (ν t : ℝ) (S : Finset PeriodicFrequency)
    (g : PeriodicFrequency → ℂ) (hg : g 0 = 0) :
    laplaceOperator (pressureOperatorOn S (heatCoeffs ν t g)) =
      heatCoeffs ν t (truncateCoeffs S g) := by
  rw [laplaceOperator_pressureOperatorOn S _ (by simpa using hg),
    truncateCoeffs_heatCoeffs]

end NSFormalization.Paper1.PeriodicPressureComposition
