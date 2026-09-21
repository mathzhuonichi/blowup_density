import Tests.ForceClasses
import NSFormalization.Section4.A04.ZeroSolution

/-! Reviewer probe: the final guarded rider is applicable to a genuine reference. -/

noncomputable section

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Tests
open scoped ENNReal

/-- At concrete positive parameters, the zero compact force and transported zero
solution satisfy every premise of the registered regular-reference rider. -/
example :
    ∃ f : SpaceTimeField, f ∈ forceClassCompact ∧
      ∃ u : ClassicalSolutionR 1 0 f 1,
        maximalLifespanR 1 0 f = ENNReal.ofReal 1 ∧
        forceSobolevENorm 1 0 (f - 0) < 1 ∧
        energyENorm 1 (u.velocity - (0 : SpaceTimeField)) < 1 ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ (1 / 2 : ℝ) →
          ∀ x : NavierStokes.ProblemStatement.Space,
            u.velocity (t, x) = (0 : SpaceTimeField) (t, x)) := by
  let v : ClassicalSolutionR 1 0 0 (1 + 1) :=
    BlowupDensity.Bindings.maximalPartial_ofA02
      (NSFormalization.Section4.A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num))
  have hg : (0 : SpaceTimeField) ∈ forceClassCompact := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    simp
  have h := checkedForceClasses.regularReference forceClassCompact (Or.inl rfl)
    1 (by norm_num) 1 (by norm_num) 1 (Or.inl rfl) 0
    (by norm_num [criticalOrder]) 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0 hg 1 (by norm_num)
    v (1 / 2 : ℝ) (by norm_num) (by norm_num) 1 1 (by norm_num) (by norm_num)
  obtain ⟨f, hf, u, hlife, hforce, henergy, hhistory⟩ := h
  have hv : v.velocity = (0 : SpaceTimeField) := rfl
  rw [hv] at henergy hhistory
  exact ⟨f, hf, u, hlife, hforce, henergy, hhistory⟩

end
