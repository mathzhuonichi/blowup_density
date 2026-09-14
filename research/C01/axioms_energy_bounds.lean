import NSFormalization.Section4.C01.EnergyBounds
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom audit for lane 154-C01-v3-bounds
(`Section4/C01/EnergyBounds.lean`).  Every declaration must depend on exactly
`[propext, Classical.choice, Quot.sound]`.

Non-vacuity: the two deliverables `energyDifferentialBound` and `l2Bound` are instantiated on
the genuine classical solution `A04.zeroSol : ClassicalSolutionR 1 0 0 2`
(`Section4/A04/ZeroSolution.lean`) with `A04.memForceR_zero`, at the interior time `1 ∈ (0,2)`
(row `energyDifferentialBound`, with `E'`/`HasDerivAt` supplied by `energyIdentity_l2Sq`) and
at `1 ∈ Ico 0 2` (row `l2Bound`), so the witnesses are not vacuous for type-theoretic reasons.
-/

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field

namespace NSFormalization.Section4.C01

-- nonnegativity / squaring helpers
#print axioms l2Sq_nonneg
#print axioms gradientSq_nonneg
#print axioms l2Sq_eq_sq_l2Norm

-- carrier-B `l2Norm = ‖·.toLp‖` bridges and Cauchy–Schwarz
#print axioms l2Norm_eq_norm_toLp_velocity
#print axioms l2Norm_eq_norm_toLp_force
#print axioms pairing_le_l2Norm_mul

-- row energyDifferentialBound (the ordinary energy inequality)
#print axioms energyDifferentialBound

-- energy continuity in time (endpoint 0 included)
#print axioms velocityL2Norm_continuousOn
#print axioms velocityL2Sq_continuousOn

-- generalized scalar regularized-division lemma
#print axioms sqrt_energy_le_primitive'

-- row l2Bound = eq:RL2
#print axioms l2Bound

-- Non-vacuity on `A04.zeroSol : ClassicalSolutionR 1 0 0 2`.
-- Row energyDifferentialBound at the interior time `1 ∈ (0,2)`, with the derivative from the
-- ordinary energy identity.
example := energyDifferentialBound (A04.zeroSol 1 2 (by norm_num) (by norm_num))
  A04.memForceR_zero (show (1 : ℝ) ∈ Ioo 0 2 from ⟨by norm_num, by norm_num⟩)
  _ (energyIdentity_l2Sq (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
      (show (1 : ℝ) ∈ Ioo 0 2 from ⟨by norm_num, by norm_num⟩))

-- Row l2Bound at `1 ∈ Ico 0 2`.
example := l2Bound (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
  (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) ∈ Ico 0 2 from ⟨by norm_num, by norm_num⟩)

end NSFormalization.Section4.C01
