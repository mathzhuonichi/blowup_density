import NSFormalization.Paper1.PeriodicFiniteVectorBound
import NSFormalization.Paper1.PeriodicLerayCoeffCore

noncomputable section
namespace NSFormalization.Paper1.PeriodicCrossComponentTransport

open NSFormalization.Paper1.PeriodicFiniteVectorBound
open NSFormalization.Paper1.PeriodicLerayCoeffCore
open scoped BigOperators

/-- The coefficient of `(u · ∇) v_i` at frequency `k` for finite Fourier data.
The derivative acts on the second factor, hence the symbol at `k-l`. -/
def transportCoeff (u v : FiniteVector) (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  ∑ j : Fin 3, ∑ l ∈ (u j).support,
    (u j l) * derivativeSymbol j (k - l) * (v i (k - l))

@[simp] theorem transportCoeff_zero_left (v : FiniteVector) (i : Fin 3)
    (k : PeriodicFrequency) :
    transportCoeff (0 : FiniteVector) v i k = 0 := by
  simp [transportCoeff]

@[simp] theorem transportCoeff_zero_right (u : FiniteVector) (i : Fin 3)
    (k : PeriodicFrequency) :
    transportCoeff u (0 : FiniteVector) i k = 0 := by
  simp [transportCoeff]

theorem norm_transportCoeff_le (u v : FiniteVector) (i : Fin 3)
    (k : PeriodicFrequency) :
    ‖transportCoeff u v i k‖ ≤
      ∑ j : Fin 3, ∑ l ∈ (u j).support,
        ‖u j l‖ * ‖derivativeSymbol j (k - l)‖ * ‖v i (k - l)‖ := by
  unfold transportCoeff
  calc
    ‖∑ j, ∑ l ∈ (u j).support,
        (u j l) * derivativeSymbol j (k - l) * v i (k - l)‖ ≤
        ∑ j : Fin 3, ‖∑ l ∈ (u j).support,
          (u j l) * derivativeSymbol j (k - l) * v i (k - l)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ l ∈ (u j).support,
          ‖u j l‖ * ‖derivativeSymbol j (k - l)‖ * ‖v i (k - l)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖∑ l ∈ (u j).support,
            (u j l) * derivativeSymbol j (k - l) * v i (k - l)‖ ≤
          ∑ l ∈ (u j).support,
            ‖(u j l) * derivativeSymbol j (k - l) * v i (k - l)‖ :=
          norm_sum_le _ _
        _ = ∑ l ∈ (u j).support,
            ‖u j l‖ * ‖derivativeSymbol j (k - l)‖ * ‖v i (k - l)‖ := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [norm_mul, norm_mul]

end NSFormalization.Paper1.PeriodicCrossComponentTransport
