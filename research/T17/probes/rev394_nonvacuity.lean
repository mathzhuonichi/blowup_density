import NSFormalization.Section3.T17.Correction
open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open NSFormalization.Section3.T17
open scoped ContDiff Topology
-- An actual local-potential witness, with a nonempty scale interval and cylinder.
example : ∃ D : NSFormalization.Section3.T16.CutoffData,
    NSFormalization.Section3.T16.LocalPotentialAPI
      (fun _ => (0 : Space)) (fun _ => (0 : Space)) {0} 0 (1/4) 1 1 D ∧
    D.ε₀ ∈ Ioc (0 : ℝ) D.ε₀ ∧
    ((0 : ℝ), (0 : Space)) ∈ fixedProfileCylinder D := by
  obtain ⟨D, hD⟩ := NSFormalization.Section3.T16.localPotential_zero
    (fun _ => (0 : Space)) {0} 0 (1/4) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (isCompact_singleton) (by intro t ht; simp)
  refine ⟨D, hD, ⟨hD.eps_pos, le_rfl⟩, ?_⟩
  change (0 : ℝ) ∈ Icc (-2 : ℝ) 2 ∧ (0 : Space) ∈ Metric.closedBall 0 D.θRadius
  exact ⟨by norm_num, by simpa using hD.theta_radius_pos.le⟩
-- Nonzero smooth reference; chart identity exercised at a nonzero scale/time.
example : ContDiff ℝ ∞ (fun _ : SpaceTime => coordinateVector (0 : Fin 3)) :=
  contDiff_const
example : NSFormalization.Paper1.CorrectionProfile.inverseScale (1/2)
    (correctionChartPoint (0 : Space) 1 (1/2) (1, coordinateVector 0) - (1, 0)) =
      (1, coordinateVector 0) := by
  exact inverseScale_correctionChartPoint 0 1 (1/2) (by norm_num) _
