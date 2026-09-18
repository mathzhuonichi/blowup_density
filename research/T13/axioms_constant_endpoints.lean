import NSFormalization.Section3.T13.ConstantEndpoints

/-!
# Lane 344 axiom conformance

Every declaration of `NSFormalization.Section3.T13.ConstantEndpoints` must
print exactly `[propext, Classical.choice, Quot.sound]`.

Run with
`cd verification && lake env lean ../research/T13/axioms_constant_endpoints.lean`.
-/

namespace NSFormalization.Section3.T13

-- §0 coordinate helpers
#print axioms continuous_spaceCoord
#print axioms abs_spaceCoord_le_norm
#print axioms npow_mul_rpow_of_pos

-- §1 the explicit constant
#print axioms norm_exp_sub_one_sq_le_sq
#print axioms norm_exp_sub_one_sq_le_four
#print axioms norm_exp_sub_one_sq_pos
#print axioms cFracRadial
#print axioms cFracRadial_nonneg
#print axioms integrableOn_cFracRadial_Ioo
#print axioms integrableOn_cFracRadial_Ici
#print axioms integrable_cFracRadial
#print axioms measurable_cFrac_integrand
#print axioms cFrac_integrand_le
#print axioms cFrac_lt_top
#print axioms cFrac_pos

-- §2 the fixed cube
#print axioms fundamentalCubeInterior
#print axioms isOpen_fundamentalCubeInterior
#print axioms isClosed_fundamentalCube
#print axioms measurableSet_fundamentalCube
#print axioms convex_fundamentalCube
#print axioms volume_frontier_fundamentalCube
#print axioms fundamentalCubeInterior_subset_interior
#print axioms interior_subset_fundamentalCubeInterior
#print axioms interior_fundamentalCube

-- §3 single-copy periodization
#print axioms latticeVector_zero
#print axioms eq_zero_of_mem_cube
#print axioms periodize_eq_of_mem_cube
#print axioms periodize_eventuallyEq
#print axioms tsupport_subset_cube
#print axioms fderiv_eq_zero_of_notMem_tsupport

-- §4 the endpoint identities
#print axioms endpoint_zero_eq
#print axioms endpoint_one_eq

-- §5 the three `LocalizationAPI` fields
#print axioms constant_pos_finite
#print axioms endpoint_zero
#print axioms endpoint_one

end NSFormalization.Section3.T13
