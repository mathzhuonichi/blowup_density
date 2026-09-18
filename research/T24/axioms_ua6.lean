import NSFormalization.Section3.T24.AffineEnergy

/-!
# Axiom audit for T24a Ua6 (`AffineEnergy.lean`)

Every declaration of `NSFormalization.Section3.T24.AffineEnergy` must print
exactly `[propext, Classical.choice, Quot.sound]`.
-/

open NSFormalization.Section3.T24

#print axioms add_rpow_two_le
#print axioms rpow_two_eLpNorm_two
#print axioms rpow_two_eLpNorm_add_le
#print axioms rpow_two_eLpNorm_le_of_bound
#print axioms enorm_spatialGradient_affineVelocity_le
#print axioms continuous_spatialDerivative_uncurry
#print axioms spatialDerivative_eq_zero_of_notMem_tsupport
#print axioms exists_bound_spatialDerivative
#print axioms enorm_spatialGradient_rpow_two_le
#print axioms rpow_two_eLpNorm_slice_le
#print axioms rpow_two_eLpNorm_gradient_slice_le
#print axioms energyEssSup_affineVelocity_lt_top
#print axioms energyGradient_affineVelocity_lt_top
#print axioms energy_finite
#print axioms energyEssSup
#print axioms energyGradient
#print axioms energyENorm
