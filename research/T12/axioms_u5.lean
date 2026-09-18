import NSFormalization.Section3.T12.GradientLSix

/-!
Axiom audit for T12 U5 (lane 400), `Section3/T12/GradientLSix.lean`.
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace NSFormalization.Section3.T12

#print axioms inverseWeight_abs_le_one
#print axioms inverseWeight_even
#print axioms homogeneousRatio_one_abs_le_one
#print axioms homogeneousDatumWeight_one_even
#print axioms periodicLpENorm_two_le_laplacian
#print axioms periodicHomogeneousENorm_one_le_sobolev_two
#print axioms periodicLpENorm_gradientTensor_le_laplacian
#print axioms contDiff_dirDeriv
#print axioms hasCompactSupport_dirDeriv
#print axioms dirDeriv_smul_eq
#print axioms dirDeriv_add_eq
#print axioms dirDeriv_cutoffMul_eq
#print axioms dirDeriv_two_cutoffMul
#print axioms lap_cutoffMul_eq
#print axioms contDiff_lap
#print axioms hasCompactSupport_lap
#print axioms exists_cutoff_lap_bound
#print axioms smoothL2_cutoffMul
#print axioms norm_coordinateVector
#print axioms norm_dirDeriv_le_norm_gradTensor
#print axioms cutoffGradBound
#print axioms cutoffGradBound_spec
#print axioms cutoffGradBound_nonneg
#print axioms norm_dirDeriv_cutoff_le
#print axioms cutoffLapBound
#print axioms cutoffLapBound_spec
#print axioms cutoffLapBound_nonneg
#print axioms leibnizConst
#print axioms leibnizConst_pos
#print axioms norm_lap_cutoffMul_le
#print axioms tsupport_cutoff_eq
#print axioms support_cutoffMul_subset
#print axioms eqOn_zero_dirDeriv
#print axioms eqOn_zero_lap
#print axioms lap_cutoffMul_eq_zero
#print axioms leibnizMajorant
#print axioms leibnizMajorant_nonneg
#print axioms norm_gradTensor_eq
#print axioms continuous_norm_gradTensor
#print axioms continuous_leibnizMajorant
#print axioms isPeriodicSpatial_gradientTensor
#print axioms isPeriodicSpatial_leibnizMajorant
#print axioms enorm_lap_cutoffMul_le
#print axioms measurable_enn_sq
#print axioms lintegral_lap_cutoffMul_le
#print axioms eLpNorm_lap_cutoffMul_le
#print axioms gradTensor_cutoffMul_eqOn
#print axioms eLpNorm_leibnizMajorant_le
#print axioms Csix
#print axioms Csix_pos
#print axioms ofReal_Csix
#print axioms gradientLSix

end NSFormalization.Section3.T12
