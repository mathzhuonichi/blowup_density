import NSFormalization.Section3.T20.H1Energy
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11 NSFormalization.Section3.T12 NSFormalization.Section3.T20
open scoped ENNReal
example : ∀ (ν : ℝ), 0 < ν → ∀ (g : SpaceTimeField), g ∈ forceClassT →
    criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν) →
    ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
      ∀ t ∈ Ioo (0 : ℝ) T, ∃ E' : ℝ,
      HasDerivAt (fun s ↦ gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (s,x))) E' t ∧
      E' + ν * laplacianSqT (fun x ↦ meanFreeVelocity g w.velocity (t,x)) ≤
      1 * ν⁻¹ * lTwoSqT (fun x ↦ meanFreeForce g (t,x)) := by
  exact hOneEnergy
