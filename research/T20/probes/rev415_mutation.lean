import NSFormalization.Section3.T20.CriticalEnergy
open Set
open NSFormalization.Section3.T20
open NSFormalization.Section4.A02
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NavierStokes.ProblemStatement
example : (∀ (ν : ℝ), 0 < ν → ∀ (g : SpaceTimeField), g ∈ forceClassT →
  ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
    ∀ t ∈ Ioo (0 : ℝ) T, ∃ E' : ℝ,
      HasDerivAt (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2) E' t ∧
      E' / 2 + (ν - (criticalTrilinearConst + 1) *
        (criticalY (meanFreeVelocity g w.velocity) t).toReal) *
        (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 ≤
      (criticalB (meanFreeForce g) t).toReal *
        (criticalY (meanFreeVelocity g w.velocity) t).toReal) := by
  exact criticalEnergy
