import Bindings.CompactClassRider
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom and non-vacuity audit for the regular-reference riders of
Corollary 4.5.  Both declarations below must report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open scoped ENNReal

#print axioms regularReference_compact
#print axioms regularReference_of_memForceR

/-- At `ν = T = 1`, zero datum and zero compact reference force, the genuine
zero solution on `[0,2)` satisfies the rider's hypotheses.  The theorem then
produces one compact force with exact lifespan one, a solution on `[0,1)`, both
strict norm bounds, and common history through `τ = 0`. -/
example :
    ∃ f : SpaceTimeField, f ∈ forceClassCompact ∧
      ∃ u : ClassicalSolutionR 1 0 f 1,
        maximalLifespanR 1 0 f = ENNReal.ofReal 1 ∧
        forceSobolevENorm 1 0 (f - 0) < 1 ∧
        energyENorm 1 (u.velocity - (0 : SpaceTimeField)) < 1 ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ 0 →
          ∀ x : NavierStokes.ProblemStatement.Space,
            u.velocity (t, x) = (0 : SpaceTimeField) (t, x)) := by
  let v : ClassicalSolutionR 1 0 0 (1 + 1) :=
    maximalPartial_ofA02
      (NSFormalization.Section4.A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num))
  have hg : (0 : SpaceTimeField) ∈ forceClassCompact := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    simp
  have h := regularReference_compact 1 (by norm_num) 1 (by norm_num)
    1 (Or.inl rfl) 0 (by norm_num [criticalOrder]) 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0 hg 1 (by norm_num)
    v 0 (by norm_num) (by norm_num) 1 1 (by norm_num) (by norm_num)
  obtain ⟨f, hf, u, hlife, hforce, henergy, hhistory⟩ := h
  have hv : v.velocity = (0 : SpaceTimeField) := rfl
  rw [hv] at henergy hhistory
  exact ⟨f, hf, u, hlife, hforce, henergy, hhistory⟩

end
