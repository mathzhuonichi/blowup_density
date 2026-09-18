import NSFormalization.Section3.T12.Cutoff

/-! Transitive axiom audit for T12 U2.  Every public declaration is expected to
use only the standard three Lean/Mathlib axioms:
`[propext, Classical.choice, Quot.sound]`.
-/

open NSFormalization.Section3.T12

#print axioms largerCube
#print axioms cutoffBump
#print axioms cutoff
#print axioms norm_le_two_of_mem_fundamentalCube
#print axioms cutoff_contDiff
#print axioms cutoff_eq_one_on_ball
#print axioms cutoff_eq_one
#print axioms cutoff_range
#print axioms tsupport_cutoff
#print axioms hasCompactSupport_cutoff
#print axioms tsupport_fderiv_cutoff
#print axioms tsupport_iteratedFDeriv_two_cutoff
#print axioms support_fderiv_cutoff_subset_shell
#print axioms support_iteratedFDeriv_two_cutoff_subset_shell
#print axioms exists_cutoff_fderiv_bound
#print axioms exists_cutoff_iteratedFDeriv_two_bound
#print axioms fderiv_cutoff_eq_zero
#print axioms iteratedFDeriv_two_cutoff_eq_zero
#print axioms cutoffMul
#print axioms contDiff_cutoffMul
#print axioms hasCompactSupport_cutoffMul
#print axioms cutoffMul_eq_on_cube
#print axioms memHInfty_cutoffMul
