import NSFormalization.Section3.T20.YBound
namespace NSFormalization.Section3.T20
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11 NSFormalization.Section3.T12
open scoped ENNReal BigOperators
def mutatedField (c : ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (g : SpaceTimeField), g ∈ forceClassT →
    criticalRho g < ENNReal.ofReal (c * ν) →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
      ∀ t ∈ Ico (0 : ℝ) T,
      criticalY (meanFreeVelocity g w.velocity) t ≤ ∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s ∧
      (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤ criticalRho g
example : mutatedField (2 * criticalSmallness) := by
  exact yBound
end NSFormalization.Section3.T20
