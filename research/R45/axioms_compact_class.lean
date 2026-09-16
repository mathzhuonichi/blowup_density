import Bindings.CompactClassDensity

/-!
Transitive-axiom and non-vacuity audit for the compact-class instances of
Corollary 4.5.  Every named declaration below must report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open scoped ENNReal

#print axioms memForceCompact_add_memForceCompact
#print axioms memForceR_of_memForceCompact
#print axioms density_compact
#print axioms zeroIff_compact

/-- The compact density theorem is inhabited at concrete positive parameters,
zero datum, exponent one, and order zero. -/
example : RelativelyDense 1 0 forceClassCompact
    (breakdownSetIn forceClassCompact 1 (fun _ => 0) 1) :=
  density_compact 1 (by norm_num) 1 (by norm_num) 1 (Or.inl rfl) 0
    (fun _ => 0) NSFormalization.Section4.A04.zero_mem_initialClassR
    (by norm_num [criticalOrder])

/-- At the same concrete parameters, apply relative density at the compact
target `g = 0` and radius one to obtain an actual breakdown force. -/
example : ∃ f : SpaceTimeField,
    f ∈ breakdownSetIn forceClassCompact 1 (fun _ => 0) 1 ∧
      forceSobolevENorm 1 0 (f - 0) < 1 := by
  have hd := density_compact 1 (by norm_num) 1 (by norm_num)
    1 (Or.inl rfl) 0 (fun _ => 0)
    NSFormalization.Section4.A04.zero_mem_initialClassR
    (by norm_num [criticalOrder])
  have hzero : (0 : SpaceTimeField) ∈ forceClassCompact := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    simp
  obtain ⟨f, hf, hdist⟩ := hd 0 hzero 1 (by norm_num)
  exact ⟨f, hf, hdist⟩
