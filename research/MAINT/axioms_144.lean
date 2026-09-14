/-
  Lane 144 (MAINT) — transitive-axiom audit for
  `NSFormalization.Section4.A04.ZeroSolution`.

  Check:  cd verification && lake env lean ../research/MAINT/axioms_144.lean
  Expect: exit 0, every `#print axioms` = [propext, Classical.choice, Quot.sound].
-/
import NSFormalization.Section4.A04.ZeroSolution

open NSFormalization.Section4.A04

#print axioms memForceR_zero
#print axioms zero_mem_initialClassR
#print axioms zeroSol
#print axioms zeroSol_velocity
#print axioms zeroSol_pressure
#print axioms sobolevNormAt_zero
#print axioms gradientSobolevNormAt_zero
#print axioms hasSmoothSobolevPath_zero
#print axioms path_zero
#print axioms jets_zero
#print axioms const_not_jets
