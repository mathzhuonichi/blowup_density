import NSFormalization.Section3.T18.Insertion

/-!
# T18 U1 axiom audit

Every declaration introduced by the canonical U1 module must have exactly
Lean's standard `[propext, Classical.choice, Quot.sound]` footprint.
-/

open NSFormalization.Section3.T18

#print axioms InsertionData
#print axioms velocity
#print axioms pressure
#print axioms force
#print axioms velocity_formula
#print axioms pressure_formula
#print axioms force_formula
#print axioms ε₀
#print axioms eps_pos
#print axioms eps_le_scaling
#print axioms eps_le_cutoff
#print axioms delta_pos
#print axioms reference_force_mem
#print axioms initial_mem
