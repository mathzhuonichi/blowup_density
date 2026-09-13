import NSFormalization.Paper1.PeriodicLerayDivergence

noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayFrequencyScale

open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open NSFormalization.Paper1.PeriodicPressureSymbol

def frequencyScale (w : PeriodicFrequency → ℝ) (g : VectorCoeff) : VectorCoeff :=
  fun k i => (w k : ℂ) * g k i

theorem projectedCoeff_frequencyScale (w : PeriodicFrequency → ℝ)
    (g : VectorCoeff) (i : Fin 3) (k : PeriodicFrequency) :
    projectedCoeff (frequencyScale w g) i k =
      (w k : ℂ) * projectedCoeff g i k := by
  simp [frequencyScale, projectedCoeff, divergenceCoeff, pressureCoeff,
    inverseSymbol]
  have hs : (∑ j : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol j k *
      ((w k : ℂ) * g k j)) = (w k : ℂ) *
        ∑ j : Fin 3, PeriodicLerayCoeffCore.derivativeSymbol j k * g k j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs]
  ring

end NSFormalization.Paper1.PeriodicLerayFrequencyScale
