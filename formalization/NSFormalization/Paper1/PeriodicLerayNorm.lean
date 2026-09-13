import NSFormalization.Paper1.PeriodicLerayLinear

/-!
# Squared Euclidean norm bound for the periodic Leray projection

The actual imaginary derivative symbols make the pressure correction
Hermitian-orthogonal to the projected field. This proves a Pythagorean identity
and nonincrease of the sum of squared component norms at every frequency.
No bound for the default Pi supremum norm is asserted.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayNorm

open NSFormalization.Paper1.PeriodicPressureSymbol
open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open scoped BigOperators ComplexConjugate

/-- Coordinate derivative symbols are purely imaginary. -/
theorem conj_derivativeSymbol (i : Fin 3) (k : PeriodicFrequency) :
    conj (PeriodicLerayCoeffCore.derivativeSymbol i k) =
      -PeriodicLerayCoeffCore.derivativeSymbol i k := by
  simp [PeriodicLerayCoeffCore.derivativeSymbol, map_ofNat]

/-- The projected coefficient field is Hermitian-orthogonal to its pressure
correction, including the constant mode. -/
theorem projected_pressure_orthogonal (g : VectorCoeff) (k : PeriodicFrequency) :
    (∑ i : Fin 3, projectedCoeff g i k *
      conj (PeriodicLerayCoeffCore.derivativeSymbol i k *
        pressureCoeff (divergenceCoeff g) k)) = 0 := by
  simp only [map_mul, conj_derivativeSymbol]
  calc
    _ = -conj (pressureCoeff (divergenceCoeff g) k) *
        (∑ i : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol i k *
          projectedCoeff g i k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [divergence_projectedCoeff, mul_zero]

/-- Orthogonal energy decomposition at one discrete frequency. -/
theorem projected_pressure_pythagorean (g : VectorCoeff) (k : PeriodicFrequency) :
    (∑ i : Fin 3, ‖g k i‖ ^ 2) =
      (∑ i : Fin 3, ‖projectedCoeff g i k‖ ^ 2) +
      ∑ i : Fin 3, ‖PeriodicLerayCoeffCore.derivativeSymbol i k *
        pressureCoeff (divergenceCoeff g) k‖ ^ 2 := by
  have hcross := congrArg Complex.re (projected_pressure_orthogonal g k)
  have hcross' : (∑ i : Fin 3, (projectedCoeff g i k *
      conj (PeriodicLerayCoeffCore.derivativeSymbol i k *
        pressureCoeff (divergenceCoeff g) k)).re) = 0 := by
    simpa using hcross
  have hsplit (i : Fin 3) : g k i = projectedCoeff g i k +
      PeriodicLerayCoeffCore.derivativeSymbol i k *
        pressureCoeff (divergenceCoeff g) k := by
    simp only [projectedCoeff, sub_add_cancel]
  simp_rw [Complex.sq_norm]
  calc
    _ = ∑ i : Fin 3, (Complex.normSq (projectedCoeff g i k) +
        Complex.normSq (PeriodicLerayCoeffCore.derivativeSymbol i k *
          pressureCoeff (divergenceCoeff g) k) +
        2 * (projectedCoeff g i k *
          conj (PeriodicLerayCoeffCore.derivativeSymbol i k *
            pressureCoeff (divergenceCoeff g) k)).re) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsplit i, Complex.normSq_add]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hcross']
      ring

/-- The actual Leray projection does not increase squared Euclidean norm. -/
theorem sum_sq_norm_projectedCoeff_le (g : VectorCoeff) (k : PeriodicFrequency) :
    (∑ i : Fin 3, ‖projectedCoeff g i k‖ ^ 2) ≤
      ∑ i : Fin 3, ‖g k i‖ ^ 2 := by
  rw [projected_pressure_pythagorean]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _))

end NSFormalization.Paper1.PeriodicLerayNorm
