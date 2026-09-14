import NSFormalization.Section4.C01.Vocabulary

/-!
Transitive-axiom audit for lane 136-C01-e2 (`Section4/C01/Vocabulary.lean`).
Every declaration must depend on exactly `[propext, Classical.choice, Quot.sound]`.
Plus a cheap non-vacuity check: the carrier `SmoothL2Field Space` is inhabited
(`zeroField`), so the hypothesis-free bridges are statements over a nonempty type.
-/

open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open EulerSmoothLimit

namespace NSFormalization.Section4.C01

#print axioms field_normSq_integrable
#print axioms l2Sq_eq_inner
#print axioms norm_toLp_sq_eq_l2Sq
#print axioms gradientSq_eq_sum
#print axioms sqrt_dirSum_sq
#print axioms pairing_eq_inner
#print axioms energyIdentity_of_carrierB

-- Non-vacuity: the carrier is inhabited, and every bridge instantiates on it.
example : Nonempty (SmoothL2Field Space) := ⟨zeroField⟩
#check (l2Sq_eq_inner (zeroField : SmoothL2Field Space))
#check (gradientSq_eq_sum (zeroField : SmoothL2Field Space))
#check (pairing_eq_inner (zeroField : SmoothL2Field Space) zeroField)

end NSFormalization.Section4.C01
