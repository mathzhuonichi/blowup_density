import NSFormalization.Section4.C01.EnergyDerivative
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom audit for lane 150-C01-e4-assembly
(`Section4/C01/EnergyDerivative.lean`).  Every declaration must depend on exactly
`[propext, Classical.choice, Quot.sound]`.

Non-vacuity: the two derivative facts are instantiated on the genuine classical solution
`A04.zeroSol : ClassicalSolutionR 1 0 0 2` (`Section4/A04/ZeroSolution.lean`) with
`A04.memForceR_zero`, over the **non-degenerate** interior window `[1/2,1] ⊂ (0,2)` (row E4,
interior point `1/4 ∈ (0,1/2)`) and at the interior time `1 ∈ (0,2)` (row energyIdentity), so
the `HasDerivAt` witnesses are not vacuous for type-theoretic reasons.
-/

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field

namespace NSFormalization.Section4.C01

-- word-bridge helper lemmas
#print axioms wordEnergy_zero
#print axioms wordInner_sum_zero

-- item 2 seed: pointwise time derivative from `velocity_smooth`
#print axioms velocity_hasDerivAt_time

-- row E4: the exact `hd` fact `energyIdentity_classical` consumes
#print axioms energyDerivative_hasDerivAt

-- row energyIdentity: E4 fed into `energyIdentity_classical`, raw-integral form
#print axioms energyIdentity_classical_unconditional

-- Non-vacuity on `A04.zeroSol : ClassicalSolutionR 1 0 0 2`.
-- Row E4 on the non-degenerate window `[1/2,1] ⊂ (0,2)` at interior point `1/4`.
example := energyDerivative_hasDerivAt (A04.zeroSol 1 2 (by norm_num) (by norm_num))
  A04.memForceR_zero (show (0:ℝ) < 1/2 by norm_num) (show (1/2:ℝ) ≤ 1 by norm_num)
  (show (1:ℝ) < 2 by norm_num)
  (show (1/4:ℝ) ∈ Ioo 0 (1 - 1/2) from ⟨by norm_num, by norm_num⟩)

-- Row energyIdentity at the interior time `1 ∈ (0,2)`.
example := energyIdentity_classical_unconditional (A04.zeroSol 1 2 (by norm_num) (by norm_num))
  A04.memForceR_zero (show (1:ℝ) ∈ Ioo 0 2 from ⟨by norm_num, by norm_num⟩)

end NSFormalization.Section4.C01
