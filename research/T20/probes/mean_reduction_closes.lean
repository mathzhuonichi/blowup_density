import NSFormalization.Section3.T20.MeanReduction

/-! Exact target-shape probes for T20 wave-1 mean reduction (U1, U2, U6).

The first three examples deliberately repeat the canonical field statements and
close them by `exact`; the final example supplies a nonzero constant Fourier mode
alongside an inhabited force class, so the hypotheses are not witnessed only by
syntactic zero fields.
-/

noncomputable section
namespace NSFormalization.Section3.T20.MeanReductionProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ico (0 : ℝ) T,
          let v := fun x ↦ meanFreeVelocity g w.velocity (t, x)
          let h := fun x ↦ meanFreeForce g (t, x)
          IsMeanZeroT v ∧ SmoothPeriodicT v ∧
            MemPeriodicHomogeneous (1 / 2) v ∧
            MemPeriodicHomogeneous (3 / 2) v ∧
            MemPeriodicHmVector 2 v ∧
            IsMeanZeroT h ∧ SmoothPeriodicT h ∧
            MemPeriodicHomogeneous (1 / 2) h ∧
            periodicLpENorm 2 h ≠ ⊤ ∧
            periodicLpENorm 2 (gradientTensor v) ≠ ⊤ ∧
            periodicLpENorm 2 (laplacian v) ≠ ⊤ := by
  exact reductionRegular

example : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal ‖meanPathT g t‖ ≤ meanForceIntegralT g t ∧
        meanForceIntegralT g t ≤ criticalRho g := by
  exact meanBound

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
          temporalDerivative (meanFreeVelocity g w.velocity) t x +
              advection (meanFreeVelocity g w.velocity) t x +
              constantTransportT (meanPathT g)
                (meanFreeVelocity g w.velocity) (t, x) -
              ν • spatialLaplacian (meanFreeVelocity g w.velocity) t x +
              pressureGradient w.pressure t x =
            meanFreeForce g (t, x) := by
  exact meanFreeEquation

/-! A concrete nonzero constant mode.  The force class is inhabited by the
zero force, while the datum itself has a nonzero zero Fourier coefficient. -/
example :
    ∃ (c : Space) (g : SpaceTimeField),
      c ≠ 0 ∧ g ∈ forceClassT ∧
        IsPeriodicDatum 1 (fun _ : Space ↦ c) (torusConstantDatum 1 c) := by
  let c : Space := coordinateVector 0
  have hc : c ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Space ↦ v (0 : Fin 3)) h
    simp [c, coordinateVector] at h0
  have hg : (0 : SpaceTimeField) ∈ forceClassT := by
    refine ⟨contDiff_const, fun _ _ _ _ ↦ rfl,
      ∅, isCompact_empty, empty_subset _, ?_⟩
    simp
  exact ⟨c, 0, hc, hg, torusConstantDatum_isDatum 1 c⟩

end NSFormalization.Section3.T20.MeanReductionProbe
