import NSFormalization.Paper1.PeriodicPressureSymbolOperator

/-! Raw Fourier symbols for the periodic Leray calculus.

This file deliberately stops at coefficient-level algebra: no reconstruction or
Sobolev boundedness claim is made here.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayCoeffCore

open NSFormalization.Paper1.PeriodicPressureSymbol
open scoped BigOperators

abbrev VectorCoeff := PeriodicFrequency → (Fin 3 → ℂ)

def derivativeSymbol (j : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (2 * Real.pi * Complex.I) * (k j : ℂ)

@[simp] theorem derivativeSymbol_zero (j : Fin 3) :
    derivativeSymbol j 0 = 0 := by
  simp [derivativeSymbol]

def divergenceCoeff (f : VectorCoeff) (k : PeriodicFrequency) : ℂ :=
  ∑ j : Fin 3, derivativeSymbol j k * f k j

theorem derivativeSymbol_mul_sum (k : PeriodicFrequency) :
    (∑ j : Fin 3, derivativeSymbol j k * derivativeSymbol j k)
      = -(laplaceEigenvalue k : ℂ) := by
  simp only [derivativeSymbol]
  have hterm (j : Fin 3) :
      (2 * Real.pi * Complex.I) * (k j : ℂ) *
          ((2 * Real.pi * Complex.I) * (k j : ℂ)) =
        -((2 * Real.pi) ^ 2 : ℂ) * (k j : ℂ) ^ 2 := by
    ring_nf
    simp [Complex.I_mul_I]
  simp_rw [hterm]
  simp [laplaceEigenvalue]
  push_cast
  rw [Finset.mul_sum]

end NSFormalization.Paper1.PeriodicLerayCoeffCore
