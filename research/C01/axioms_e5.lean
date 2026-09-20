import NSFormalization.Section4.C01.Enstrophy
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom audit for lane 163-C01-e5-enstrophy.  Every declaration below must print
exactly `[propext, Classical.choice, Quot.sound]`.

Non-vacuity instantiates both derivative forms and the integration-by-parts value identity
on the genuine solution `A04.zeroSol : ClassicalSolutionR 1 0 0 2`, using
`A04.memForceR_zero`, on the non-degenerate window `[1/2,1] ⊂ (0,2)` and at the interior
time `1`.
-/

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev

namespace NSFormalization.Section4.C01

#print axioms wordEnergy_one
#print axioms wordInner_sum_one
#print axioms enstrophyDerivative_hasDerivAt
#print axioms directional_pairing_sum_eq_neg_laplacian
#print axioms enstrophyDerivative_eq_neg_laplacian
#print axioms enstrophyDerivative_classical_unconditional

example := enstrophyDerivative_hasDerivAt (A04.zeroSol 1 2 (by norm_num) (by norm_num))
  A04.memForceR_zero (show (0 : ℝ) < 1 / 2 by norm_num)
  (show (1 / 2 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)
  (show (1 / 4 : ℝ) ∈ Ioo 0 (1 - 1 / 2) from ⟨by norm_num, by norm_num⟩)

example := enstrophyDerivative_eq_neg_laplacian
  (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
  (show (1 : ℝ) ∈ Ioo 0 2 from ⟨by norm_num, by norm_num⟩)

example := enstrophyDerivative_classical_unconditional
  (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
  (show (1 : ℝ) ∈ Ioo 0 2 from ⟨by norm_num, by norm_num⟩)

end NSFormalization.Section4.C01
