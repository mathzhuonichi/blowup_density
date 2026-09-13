import NSFormalization.Paper1.PeriodicPicardBilinear
import NSFormalization.Paper1.PeriodicWeightShift

noncomputable section
namespace NSFormalization.Paper1.PeriodicWeightedFinsupp

open NSFormalization.Paper1.PeriodicPicardBilinear
open NSFormalization.Paper1

/-- Integer-power weighted finite Fourier sequence. -/
def weightedCoeff (r : ℕ) (f : FiniteFourier) : FiniteFourier :=
  Finsupp.onFinset f.support
    (fun k => ((periodicFrequencyWeight k : ℝ) ^ r : ℂ) * f k)
    (by intro k hk; exact (Finsupp.mem_support_iff.mpr (by
      intro hz; simp [hz] at hk)))

@[simp] theorem weightedCoeff_apply (r : ℕ) (f : FiniteFourier)
    (k : PeriodicFrequency) :
    weightedCoeff r f k = ((periodicFrequencyWeight k : ℝ) ^ r : ℂ) * f k := by
  classical
  simp [weightedCoeff]

theorem weightedCoeff_support_subset (r : ℕ) (f : FiniteFourier) :
    (weightedCoeff r f).support ⊆ f.support := by
  intro k hk
  by_contra hnot
  have hz : f k = 0 := Finsupp.notMem_support_iff.mp hnot
  simp [weightedCoeff_apply, hz] at hk

@[simp] theorem weightedCoeff_zero (r : ℕ) :
    weightedCoeff r (0 : FiniteFourier) = 0 := by
  ext k
  simp [weightedCoeff_apply]

end NSFormalization.Paper1.PeriodicWeightedFinsupp
