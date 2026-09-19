import NSFormalization.Section3.T18.EnergyRate

/-!
# Review 443: intentional negative mutation

This probe widens the main theorem's scale interval from `(0, ε₀]` to
`(-1, ε₀]`.  It is intentionally expected not to elaborate: the canonical
proof requires the load-bearing positivity premise `0 < ε`.
-/

namespace NSFormalization.Section3.T18

open Set
open NSFormalization.Section3.T10

example (data : InsertionData) (hM : 0 ≤ data.energyBound)
    (hD : 0 ≤ data.dissipationBound) :
    ∀ ε ∈ Ioc (-1 : ℝ) (ε₀ data),
      energyENormT data.place.T
          (fun z => velocity data ε z - data.reference.velocity z) ≤
        ENNReal.ofReal ((data.energyBound + data.dissipationBound) *
          ε ^ ((1 : ℝ) / 2) +
          data.correction.energyConst * ε ^ ((3 : ℝ) / 2)) := by
  intro ε hε
  exact energyRate data hM hD ε hε

end NSFormalization.Section3.T18
