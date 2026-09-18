import NSFormalization.Section3.T13.WholeSpaceIdentity

/-!
# Lane 348 transitive-axiom audit

Every public declaration of
`NSFormalization.Section3.T13.WholeSpaceIdentity` must depend only on the three
standard axioms `[propext, Classical.choice, Quot.sound]`.  The private
`exists_rotation` is audited transitively through `lintegral_kernel_smul` and
`wholeSpace_identity`.
-/

open NSFormalization.Section3.T13

#print axioms dotHomogeneousENorm_eq_homogeneousFourierENorm
#print axioms homogeneousFourierENorm_lt_top
#print axioms homogeneousFourierENorm_sq
#print axioms schwartz_lintegral_normSq
#print axioms lintegral_angularFourier_sq
#print axioms angularFourier_translate
#print axioms angularFourier_sub
#print axioms angularFourier_diff
#print axioms per_h_component
#print axioms lintegral_kernel_smul
#print axioms ofReal_normSq_eq_sum
#print axioms continuous_angularFourier_component
#print axioms component_integral_eq
#print axioms IReal_decomp
#print axioms IReal_eq_cFrac_mul_homogeneousFourierENorm_sq
#print axioms wholeSpace_identity
#print axioms measurable_phase
#print axioms norm_phase_le
#print axioms integrable_phase_mul
#print axioms contDiff_translate
#print axioms hasCompactSupport_translate
#print axioms contDiff_diff
#print axioms hasCompactSupport_diff
#print axioms measurable_kernel
#print axioms continuous_phase
#print axioms measurable_weightedSq
