import NSFormalization.Section4.R42.PressureGradient

open NSFormalization.Section4.R42

-- #print axioms for every public declaration of the PressureGradient module.
-- Expected for each: [propext, Classical.choice, Quot.sound]
#print axioms contDiff_slice_pressure
#print axioms memLp_pressureGradient_of_compact
#print axioms memLp_pressureGradient_add
#print axioms memLp_pressureGradient_of_difference_support
