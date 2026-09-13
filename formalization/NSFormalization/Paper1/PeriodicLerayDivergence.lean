import NSFormalization.Paper1.PeriodicLerayCoeffCore

/-! Coefficient-level divergence cancellation for the periodic Leray correction. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayDivergence

open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicPressureSymbol
open scoped BigOperators

/-- Raw Fourier Leray correction using the zero-mean inverse pressure coefficient. -/
def projectedCoeff (f : VectorCoeff) (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  f k i - PeriodicLerayCoeffCore.derivativeSymbol i k * pressureCoeff (divergenceCoeff f) k

def projectedWithPressure (f : VectorCoeff) (p : PeriodicFrequency → ℂ)
    (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  f k i - PeriodicLerayCoeffCore.derivativeSymbol i k * p k

/-- The raw divergence has zero zero-mode because every derivative symbol vanishes there. -/
theorem divergenceCoeff_zero_mode (f : VectorCoeff) : divergenceCoeff f 0 = 0 := by
  simp [divergenceCoeff, PeriodicLerayCoeffCore.derivativeSymbol]

/-- The zero-mean inverse pressure solves the raw coefficient equation, including the zero mode. -/
theorem pressureCoeff_divergence_equation_compatible (f : VectorCoeff)
    (k : PeriodicFrequency) :
    -(laplaceEigenvalue k : ℂ) * pressureCoeff (divergenceCoeff f) k =
      divergenceCoeff f k := by
  exact pressureCoeff_equation (divergenceCoeff f) (divergenceCoeff_zero_mode f) k

/-- A raw coefficient pressure satisfying the inverse-Laplacian equation removes divergence.
This is purely coefficient-level and does not assert existence of a physical pressure field. -/
@[simp] theorem projectedWithPressure_zero (f : VectorCoeff)
    (p : PeriodicFrequency → ℂ) (i : Fin 3) :
    projectedWithPressure f p i 0 = f 0 i := by
  simp [projectedWithPressure, PeriodicLerayCoeffCore.derivativeSymbol]

theorem divergence_projectedWithPressure (f : VectorCoeff)
    (p : PeriodicFrequency → ℂ)
    (hp : ∀ k, -(laplaceEigenvalue k : ℂ) * p k = divergenceCoeff f k)
    (k : PeriodicFrequency) :
    ∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
      projectedWithPressure f p i k = 0 := by
  unfold projectedWithPressure
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hs : (∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
      (PeriodicLerayCoeffCore.derivativeSymbol i k * p k)) =
      (∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
        PeriodicLerayCoeffCore.derivativeSymbol i k) * p k := by
    calc
      _ = ∑ i : Fin 3, (PeriodicLerayCoeffCore.derivativeSymbol i k *
          PeriodicLerayCoeffCore.derivativeSymbol i k) * p k := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.sum_mul]
  rw [hs, derivativeSymbol_mul_sum]
  rw [hp k]
  simp [divergenceCoeff]

theorem projectedWithPressure_divergence_free (f : VectorCoeff)
    (p : PeriodicFrequency → ℂ)
    (hp : ∀ k, -(laplaceEigenvalue k : ℂ) * p k = divergenceCoeff f k)
    (k : PeriodicFrequency) :
    ∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
      projectedWithPressure f p i k = 0 :=
  divergence_projectedWithPressure f p hp k


/-- The normalized inverse-pressure correction is divergence-free via the compatible equation. -/
theorem divergence_projectedCoeff_via_pressure_equation (f : VectorCoeff)
    (k : PeriodicFrequency) :
    ∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
      projectedWithPressure f (pressureCoeff (divergenceCoeff f)) i k = 0 := by
  exact divergence_projectedWithPressure f (pressureCoeff (divergenceCoeff f))
    (pressureCoeff_divergence_equation_compatible f) k

/-- The corrected coefficient has zero divergence at every frequency. --/
theorem divergence_projectedCoeff (f : VectorCoeff) (k : PeriodicFrequency) :
    ∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k * projectedCoeff f i k = 0 := by
  unfold projectedCoeff
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfactor :
      (∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k * PeriodicLerayCoeffCore.derivativeSymbol i k) *
          pressureCoeff (divergenceCoeff f) k =
        (-(laplaceEigenvalue k : ℂ)) * pressureCoeff (divergenceCoeff f) k := by
    rw [derivativeSymbol_mul_sum]
  calc
    (∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k * f k i) -
        ∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
          (PeriodicLerayCoeffCore.derivativeSymbol i k * pressureCoeff (divergenceCoeff f) k) =
      divergenceCoeff f k -
        (∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k * PeriodicLerayCoeffCore.derivativeSymbol i k) *
          pressureCoeff (divergenceCoeff f) k := by
            simp only [divergenceCoeff]
            have hs : (∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
                (PeriodicLerayCoeffCore.derivativeSymbol i k * pressureCoeff (divergenceCoeff f) k)) =
                (∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
                  PeriodicLerayCoeffCore.derivativeSymbol i k) * pressureCoeff (divergenceCoeff f) k := by
              calc
                _ = ∑ i : Fin 3, (PeriodicLerayCoeffCore.derivativeSymbol i k *
                    PeriodicLerayCoeffCore.derivativeSymbol i k) * pressureCoeff (divergenceCoeff f) k := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
                _ = _ := by rw [Finset.sum_mul]
            rw [hs]
    _ = divergenceCoeff f k -
        (-(laplaceEigenvalue k : ℂ)) * pressureCoeff (divergenceCoeff f) k := by rw [hfactor]
    _ = 0 := by
      have hg : divergenceCoeff f 0 = 0 := by
        simp [divergenceCoeff, PeriodicLerayCoeffCore.derivativeSymbol]
      rw [pressureCoeff_equation (divergenceCoeff f) hg]
      simp

end NSFormalization.Paper1.PeriodicLerayDivergence

namespace NSFormalization.Paper1.PeriodicLerayDivergence

open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicPressureSymbol
open scoped BigOperators

@[simp] theorem projectedCoeff_zero (f : VectorCoeff) (i : Fin 3) :
    projectedCoeff f i 0 = f 0 i := by
  simp [projectedCoeff, PeriodicLerayCoeffCore.derivativeSymbol]

/-- A divergence-free raw coefficient field is unchanged by the pressure correction. -/
theorem projectedCoeff_eq_of_divergence_zero (f : VectorCoeff)
    (hdiv : ∀ k, divergenceCoeff f k = 0) :
    ∀ i k, projectedCoeff f i k = f k i := by
  intro i k
  simp [projectedCoeff, pressureCoeff, hdiv k]

end NSFormalization.Paper1.PeriodicLerayDivergence
