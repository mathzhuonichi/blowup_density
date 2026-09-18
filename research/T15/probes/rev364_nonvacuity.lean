import NSFormalization.Section3.T15.HaarBridge
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/- Reviewer non-vacuity check for the concrete bump used by the lane probe. -/
noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open scoped ContDiff ENNReal

def revProbeCenter : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

def revProbeBump : ContDiffBump revProbeCenter :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def revProbeField : SpatialField :=
  fun x => (revProbeBump x) • coordinateVector 0

example : revProbeField revProbeCenter ≠ 0 := by
  have h1 : revProbeBump revProbeCenter = 1 :=
    revProbeBump.one_of_mem_closedBall
      (Metric.mem_closedBall_self revProbeBump.rIn_pos.le)
  have h2 : revProbeField revProbeCenter = coordinateVector 0 := by
    simp [revProbeField, h1]
  rw [h2]
  intro hcon
  have hz : (coordinateVector (0 : Fin 3)) 0 = 0 := by rw [hcon]; rfl
  rw [coordinateVector] at hz
  simp at hz
