import Tests.ForceClasses

/-!
Transitive-axiom and concrete-consumer audit for the registered Corollary 4.5
contract. Every named declaration below must report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open BlowupDensity.Tests
open scoped ENNReal

#print axioms density
#print axioms zeroIff
#print axioms schwartzDensity
#print axioms regularReference_compact
#print axioms regularReference_rapid
#print axioms regularReference
#print axioms forceClasses
#print axioms checkedForceClasses

/-- The checked guarded field selects the compact class and produces genuine
by-time-one breakdown density at a concrete subcritical order. -/
example : RelativelyDense 1 0 forceClassCompact
    (breakdownSetIn forceClassCompact 1 (fun _ => 0) 1) :=
  checkedForceClasses.density forceClassCompact (Or.inl rfl)
    1 (by norm_num) 1 (by norm_num) 1 (Or.inl rfl) 0 (fun _ => 0)
    NSFormalization.Section4.A04.zero_mem_initialClassR
    (by norm_num [criticalOrder])

/-- The same checked guarded field selects the rapid class without changing
the datum, threshold, or breakdown predicate. -/
example : RelativelyDense 2 (-1) forceClassRapid
    (breakdownSetIn forceClassRapid 1 (fun _ => 0) 1) :=
  checkedForceClasses.density forceClassRapid (Or.inr rfl)
    1 (by norm_num) 1 (by norm_num) 2 (Or.inr rfl) (-1) (fun _ => 0)
    NSFormalization.Section4.A04.zero_mem_initialClassR
    (by norm_num [criticalOrder])
