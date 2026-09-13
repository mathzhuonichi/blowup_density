import NSFormalization.Paper1.PeriodicCriticalBoxConvergence

/-!
# Explicit dyadic lattice-shell counting

The finite critical interfaces carry a square-root cardinality loss.  This file
records the exact size of a dyadic integer-frequency shell.  It is a concrete
obstruction to removing that loss by cardinality estimates alone: the shell
cardinality grows cubically with the radius.  No Sobolev embedding or PDE
conclusion is asserted.
-/
noncomputable section
namespace NSFormalization.Paper1

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open Set Filter
open scoped BigOperators

/-- Frequencies in the radius-`R` box but outside the radius-`⌊R/2⌋` box. -/
def periodicFrequencyDyadicShell (R : ℕ) : Finset PeriodicFrequency :=
  periodicFrequencyBox R \ periodicFrequencyBox (R / 2)

lemma periodicFrequencyBox_half_subset_box (R : ℕ) :
    periodicFrequencyBox (R / 2) ⊆ periodicFrequencyBox R := by
  exact monotone_periodicFrequencyBox (Nat.div_le_self R 2)

/-- Exact cardinality of the dyadic shell. -/
theorem card_periodicFrequencyDyadicShell (R : ℕ) :
    (periodicFrequencyDyadicShell R).card =
      (2 * R + 1) ^ 3 - (2 * (R / 2) + 1) ^ 3 := by
  unfold periodicFrequencyDyadicShell
  rw [Finset.card_sdiff]
  have hinter : periodicFrequencyBox (R / 2) ∩ periodicFrequencyBox R =
      periodicFrequencyBox (R / 2) := by
    exact Finset.inter_eq_left.mpr (periodicFrequencyBox_half_subset_box R)
  rw [hinter, card_periodicFrequencyBox, card_periodicFrequencyBox]

end NSFormalization.Paper1

