import NSFormalization.Section4.C01.EnergyBounds
import NSFormalization.Section4.A04.ZeroSolution

/-! REVIEW PROBE (lane 154): `l2Bound` really covers the left endpoint `t = 0` of `Ico 0 T`
(the `S = 0` degenerate application of `sqrt_energy_le_primitive'`), and the axioms of the
`Icc`-counterexample probe are standard. -/

open Set MeasureTheory

namespace NSFormalization.Section4.C01

example : l2Norm (slice (A04.zeroSol 1 2 (by norm_num) (by norm_num)).velocity 0)
    ≤ energyBudget 0 0 0 :=
  l2Bound (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
    (by norm_num) (show (0 : ℝ) ∈ Ico 0 2 from ⟨le_rfl, by norm_num⟩)

end NSFormalization.Section4.C01
