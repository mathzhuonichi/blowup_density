import NSFormalization.Section3.T22.CutoffKernel

/-!
Transitive-axiom audit for T22 U-A2 (`Section3/T22/CutoffKernel.lean`).
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
-/

open NSFormalization.Section3.T22

#print axioms integrable_weighted_schwartz
#print axioms cutoffSchwartz
#print axioms cutoffSchwartz_apply
#print axioms integrable_weighted_fourier_cutoff
#print axioms integrable_weighted_fourier_cutoff_mathlib
#print axioms lintegral_weighted_fourier_cutoff_ne_top
