import Tests.TorusLocalTheoryV2
import Tests.ContinuationV3
import NSFormalization.Section3.T11.H1RestartBeyond

/-!
# B5 T³ registered continuation probe

Both domain registrations have only the standard logical axioms.  The new
periodic endpoint field is instantiated below at Sobolev order one on the
genuine zero solution.
-/

#print axioms BlowupDensity.Tests.checkedTorusLocalTheoryV2
#print axioms BlowupDensity.Tests.checkedContinuationV3
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Tests.checkedTorusLocalTheoryV2
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Tests.checkedContinuationV3

noncomputable section

namespace BlowupDensity.Research.P21.B5TRegisteredProbe

open Set MeasureTheory NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

private theorem zeroDatum (s : ℝ) :
    IsPeriodicDatum s (0 : SpatialField) (0 : PeriodicSobolev s) := by
  refine ⟨fun _ _ => rfl, integrable_const 0, ?_⟩
  intro i k
  change (0 : ℂ) = periodicFrequencyWeight k ^ (s / 2) •
    periodicFourierCoeff (fun _ : Space => (0 : ℂ)) k
  rw [periodicFourierCoeff_const]
  simp

/-- The canonical zero velocity and pressure form a periodic classical
solution on every positive horizon. -/
private def zeroSolution (T : ℝ) (hT : 0 < T) :
    NSFormalization.Section3.T10.ClassicalSolutionT 1 0 0 T where
  velocity := 0
  pressure := 0
  horizon_pos := hT
  velocity_smooth := contDiff_const.contDiffOn
  pressure_smooth := contDiff_const.contDiffOn
  initial := by simp
  divergence := by intros; simp [spatialDivergence, spatialDerivative]
  momentum := by
    intros
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative,
      advection, spatialDerivative, spatialLaplacian, pressureGradient]
  sobolev := fun m => ⟨fun _ => 0, continuousOn_const, fun _ _ => zeroDatum m⟩
  pressure_gradient := by
    intro t ht
    have he : (fun x : Space =>
        pressureGradient (0 : NSFormalization.Section4.A02.SpaceTimeScalar) t x) = 0 := by
      funext x
      simp [pressureGradient]
    rw [he]
    change MemLp (fun _ : PeriodicTorus => (0 : Space)) 2 periodicTorusMeasure
    exact memLp_const 0
  velocity_periodic := fun _ _ _ _ => rfl
  pressure_periodic := fun _ _ _ _ => rfl
  pressure_gauge := by
    simp [NSFormalization.Section3.T10.PressureGaugeT,
      NSFormalization.Section3.T10.pressureMeanT,
      NSFormalization.Section3.T10.torusLift,
      NSFormalization.Paper1.torusLift]

private theorem zeroForce :
    (0 : SpaceTimeField) ∈
      BlowupDensity.Contracts.V1.TorusLocalTheory.forceClassT := by
  refine ⟨contDiff_const, fun _ _ _ _ => rfl, ∅, isCompact_empty,
    empty_subset _, ?_⟩
  simp

private theorem zeroInitial :
    (0 : SpatialField) ∈
      BlowupDensity.Contracts.V1.TorusLocalTheory.initialClassT := by
  refine ⟨contDiff_const, fun _ _ => rfl, ?_⟩
  intro x
  simp [spatialDivergence, spatialDerivative]

private theorem zeroSolvesBelow :
    BlowupDensity.Contracts.V1.TorusLocalTheory.SolvesBelowT 1 0 0 1 0 0 := by
  intro b hb _hb1
  exact ⟨BlowupDensity.Bindings.TorusLocalTheory.toContract (zeroSolution b hb),
    rfl, rfl⟩

/-- Non-vacuity: the registered order-one endpoint theorem returns a larger
solution for the zero trajectory, with literal zero velocity and normalized
pressure on the old interval. -/
example : ∃ δ : ℝ, 0 < δ ∧
    ∃ v : BlowupDensity.Contracts.V1.TorusLocalTheory.ClassicalSolutionT
        1 0 0 (1 + δ),
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, v.velocity (t, x) = 0) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, v.pressure (t, x) = 0) := by
  let K := BlowupDensity.Contracts.V1.TorusData.periodicSobolevENorm
    1 (0 : SpatialField)
  have hK : K ≠ ⊤ := by
    dsimp only [K]
    change NSFormalization.Section3.T10.periodicSobolevENorm 1
      (0 : SpatialField) ≠ ⊤
    exact NSFormalization.Section3.T11.periodicSobolevENorm_ne_top_smooth
      1 contDiff_const (fun _ _ => rfl)
  obtain ⟨δ, hδ, hr⟩ :=
    BlowupDensity.Tests.checkedTorusLocalTheoryV2.2.restartBeyond
      1 one_pos 0 zeroForce 1 one_pos K hK
  obtain ⟨v, hv, hp⟩ := hr 0 zeroInitial 0 0 zeroSolvesBelow
    (by
      intro t ht
      change BlowupDensity.Contracts.V1.TorusData.periodicSobolevENorm
        1 (0 : SpatialField) ≤ K
      exact le_rfl)
  exact ⟨δ, hδ, v, hv, hp⟩

end BlowupDensity.Research.P21.B5TRegisteredProbe
