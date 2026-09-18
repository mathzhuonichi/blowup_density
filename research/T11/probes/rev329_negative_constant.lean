import NSFormalization.Section3.T11.FractionalSmoothing

/-
Negative reviewer probe: the main symbol statement is substantively mutated by
removing the `(3/4) * exp (-1)` term from the constant.  The original theorem
must not typecheck as a proof of this stronger (and false at nonzero modes)
bound.  This file is intentionally expected to fail.
-/
noncomputable section

namespace NSFormalization.Section3.T11.Rev329Negative

open NSFormalization.Section3.T10
open NSFormalization.Section3.T11

example {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (k : PeriodicFrequency) :
    torusFracSymbol ν t k ≤ (ν * T) ^ (3 / 4 : ℝ) * torusFracKernel ν t := by
  exact torusFracSymbol_le hν ht htT k

end NSFormalization.Section3.T11.Rev329Negative
