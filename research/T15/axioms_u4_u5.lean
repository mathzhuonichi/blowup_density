import NSFormalization.Section3.T15.Energy
import NSFormalization.Section3.T15.Mixed

/-!
# T15 U4/U5 transitive-axiom audit

Every declaration of `formalization/NSFormalization/Section3/T15/Energy.lean`
and `formalization/NSFormalization/Section3/T15/Mixed.lean`.  Each line must
print exactly `'...' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Run from `verification/` with
`lake env lean ../research/T15/axioms_u4_u5.lean`.
-/

open NSFormalization.Section3.T15

-- Energy.lean (U4)
#print axioms torusChart_mem_fundamentalCube
#print axioms torusLift_congr_cube
#print axioms contDiff_periodize_of_subset_interior
#print axioms memLp_torusLift_gradientVector
#print axioms scaledVelocity_slice_contDiff
#print axioms energySlices_memLp
#print axioms packetEnergyIdentity
#print axioms packetDissipationIdentity

-- Mixed.lean (U5)
#print axioms torusChart
#print axioms torusLift_eq_comp
#print axioms measurable_torusChart
#print axioms torusChart_coe
#print axioms lintegral_comp_torusChart
#print axioms map_torusChart
#print axioms eLpNorm_torusLift_eq_restrict
#print axioms eLpNorm_torusLift_eq_volume
#print axioms mixedLebesgueENorm_eq
#print axioms continuous_slice
#print axioms torusSlicePath
#print axioms enorm_torusSlicePath
#print axioms continuous_torusSlicePath
#print axioms mixedLebesgueENormT_eq
#print axioms scaledForce_contDiff
#print axioms scaledForce_hasCompactSupport
#print axioms scaledForce_slice_tsupport_cube
#print axioms torusLift_periodizedScaledForce
#print axioms mixedLebesgueENormT_periodizedScaledForce
#print axioms mixed_memLp
#print axioms packetMixedScaling
