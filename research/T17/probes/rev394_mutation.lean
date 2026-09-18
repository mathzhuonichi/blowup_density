import NSFormalization.Section3.T17.Correction
open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open NSFormalization.Section3.T17
open scoped ContDiff Topology
-- Mutate the affine chart's time coefficient from 1 to 2.
example (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0) (z : SpaceTime) :
    NSFormalization.Paper1.CorrectionProfile.inverseScale ε
      ((T + 2 * ε ^ 2 * z.1, x₀ + ε • z.2) - (T, x₀)) = z := by
  exact inverseScale_correctionChartPoint x₀ T ε hε z

-- Main API bound mutation: replace temporal-support coefficient 4 by 2.
example {ν : ℝ} {u : VelocityField} {p : PressureField} {f : VelocityField}
    {K : Set Space} {place : NSFormalization.Section3.T15.PlacementData u p f K}
    {v : SpaceTimeField} {r δ : ℝ} {D : NSFormalization.Section3.T16.CutoffData}
    (h : CorrectionAPI ν place v r δ D) (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) :
    volume (torusTemporalSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (2 * ε ^ 2) := by
  exact h.force_time_length ε hε
