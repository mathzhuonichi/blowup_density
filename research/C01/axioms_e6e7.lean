import NSFormalization.Section4.C01.EnstrophyIdentityRaw
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom audit for lane 170-C01-e6-e7-enstrophy-identity.  Every declaration below
must print exactly `[propext, Classical.choice, Quot.sound]`.

The non-vacuity examples instantiate the pressure cancellation, both full enstrophy
identities, and the absorption-shaped H² finiteness theorem on the genuine solution
`A04.zeroSol : ClassicalSolutionR 1 0 0 2`, with the genuine force witness
`A04.memForceR_zero` and the nonempty time interval `(0,1)`.
-/

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open scoped ENNReal

namespace NSFormalization.Section4.C01

#print axioms laplacianField_divergence_zero
#print axioms laplacian_pressure_pairing_zero
#print axioms inner_enstrophy_identity_deriv
#print axioms enstrophyDerivative_value_classical
#print axioms enstrophyIdentity_classical
#print axioms enstrophyIdentity_gradientSq
#print axioms h2TimeIntegral_strict
#print axioms squaredHTwoIntegral_strict
#print axioms h2TimeIntegral_of_absorption

example := laplacian_pressure_pairing_zero
  (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
  (show (1 : ℝ) ∈ Ioo 0 2 from ⟨by norm_num, by norm_num⟩)

example := enstrophyIdentity_classical
  (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
  (show (1 : ℝ) ∈ Ioo 0 2 from ⟨by norm_num, by norm_num⟩)

example := enstrophyIdentity_gradientSq
  (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
  (show (1 : ℝ) ∈ Ioo 0 2 from ⟨by norm_num, by norm_num⟩)

example := h2TimeIntegral_of_absorption
  (ν := 1) (a := (0 : A02.SpatialField)) (f := (0 : A02.SpaceTimeField)) (T := 2)
  (by norm_num) A04.zero_mem_initialClassR A04.memForceR_zero
  (A04.zeroSol 1 2 (by norm_num) (by norm_num))
  (S := 1) (by norm_num) (by norm_num) (by
    intro t _ht
    change ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const *
      eLpNorm (0 : A02.SpatialField) 3 volume ≤ ENNReal.ofReal ((1 : ℝ) / 4)
    simp)

end NSFormalization.Section4.C01
