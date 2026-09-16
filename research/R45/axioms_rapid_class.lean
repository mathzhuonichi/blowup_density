import Bindings.RapidClassDensity

/-!
Transitive-axiom and non-vacuity audit for the rapid-class instances of
Corollary 4.5.  Every named declaration below must report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open scoped ENNReal

#print axioms density_rapid
#print axioms zeroIff_rapid
#print axioms regularReference_rapid
#print axioms schwartzDensity
#print axioms density
#print axioms zeroIff

/-- The Schwartz specialization is inhabited at `ν = T = 1`, zero datum,
exponent one, and order zero. -/
example : RelativelyDense 1 0 forceClassRapid
    (breakdownSetIn forceClassRapid 1 (fun _ => 0) 1) := by
  apply schwartzDensity 1 (by norm_num) 1 (by norm_num) 1 (Or.inl rfl) 0
    (fun _ => 0)
  · refine ⟨⟨0, ?_⟩, ?_⟩
    · funext x
      simp
    intro x
    simp [NavierStokes.ProblemStatement.spatialDivergence,
      NavierStokes.ProblemStatement.spatialDerivative]
  · norm_num [criticalOrder]

/-- At the same concrete parameters, apply rapid relative density at the
rapid target `g = 0` and radius one to obtain an actual breakdown force. -/
example : ∃ f : SpaceTimeField,
    f ∈ breakdownSetIn forceClassRapid 1 (fun _ => 0) 1 ∧
      forceSobolevENorm 1 0 (f - 0) < 1 := by
  have hd := density_rapid 1 (by norm_num) 1 (by norm_num)
    1 (Or.inl rfl) 0 (fun _ => 0)
    NSFormalization.Section4.A04.zero_mem_initialClassR
    (by norm_num [criticalOrder])
  have hzero : (0 : SpaceTimeField) ∈ forceClassRapid := by
    refine ⟨contDiffOn_const, fun N k => ⟨0, fun t ht x => ?_⟩⟩
    simp
  obtain ⟨f, hf, hdist⟩ := hd 0 hzero 1 (by norm_num)
  exact ⟨f, hf, hdist⟩

/-- The regular-reference rider has a genuine concrete reference at
`ν = T = 1`, `a = g = 0`: the transported zero classical solution on horizon
`2 = T + δ`. -/
example : ∃ v : ClassicalSolutionR 1 (fun _ => 0) 0 (1 + 1),
    ∃ f : SpaceTimeField, f ∈ forceClassRapid ∧
      ∃ u : ClassicalSolutionR 1 (fun _ => 0) f 1,
        maximalLifespanR 1 (fun _ => 0) f = ENNReal.ofReal 1 ∧
        forceSobolevENorm 1 0 (f - 0) < 1 ∧
        energyENorm 1 (u.velocity - v.velocity) < 1 ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ 0 →
          ∀ x : NavierStokes.ProblemStatement.Space,
            u.velocity (t, x) = v.velocity (t, x)) := by
  let v : ClassicalSolutionR 1 (fun _ => 0) 0 (1 + 1) :=
    maximalPartial_ofA02
      (NSFormalization.Section4.A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num))
  refine ⟨v, ?_⟩
  have hzero : (0 : SpaceTimeField) ∈ forceClassRapid := by
    refine ⟨contDiffOn_const, fun N k => ⟨0, fun t ht x => ?_⟩⟩
    simp
  exact regularReference_rapid 1 (by norm_num) 1 (by norm_num)
    1 (Or.inl rfl) 0 (by norm_num [criticalOrder])
    (fun _ => 0) NSFormalization.Section4.A04.zero_mem_initialClassR
    0 hzero 1 (by norm_num) v 0 (by norm_num) (by norm_num)
    1 1 (by norm_num) (by norm_num)
