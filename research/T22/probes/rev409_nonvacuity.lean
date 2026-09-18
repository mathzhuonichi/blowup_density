import NSFormalization.Section3.T22.CutoffDatum

/-! Reviewer non-vacuity probe: choose the actual smooth cutoff produced by
    `exists_cutoff` on a concrete compact-in-open pair and use it with the zero
    field and zero datum.  No cutoff hypotheses are assumed externally. -/

noncomputable section

open Set MeasureTheory Filter Metric
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T22
open scoped ContDiff ENNReal SchwartzMap Topology

def rev409Ω : Set Space := ball (0 : Space) 1
def rev409K : Set Space := closedBall (0 : Space) (1 / 2)

theorem rev409Ω_open : IsOpen rev409Ω := isOpen_ball
theorem rev409K_compact : IsCompact rev409K := isCompact_closedBall _ _
theorem rev409K_subset : rev409K ⊆ rev409Ω := closedBall_subset_ball (by norm_num)

theorem rev409_isCutoffDatum_zero (s : ℝ) (χ : Space → ℝ) :
    IsCutoffDatum s χ (0 : RealVectorSobolev s) (0 : RealVectorSobolev s) := by
  intro i ψ
  simp

theorem rev409_zeroExtension_zero (Ω : Set Space) :
    zeroExtension Ω (fun _ => (0 : Space)) = fun _ => (0 : Space) := by
  funext x
  by_cases hx : x ∈ Ω <;> simp [zeroExtension, hx]

theorem rev409_zero_nonvacuous :
    IsSobolevDatum 0 (zeroExtension rev409Ω (fun _ => (0 : Space)))
      (0 : RealVectorSobolev 0) := by
  obtain ⟨χ, hχs, hχc, hχΩ, hχ1⟩ :=
    exists_cutoff rev409Ω_open rev409K_compact rev409K_subset
  refine isCutoffDatum_realizes_zeroExtension hχs hχc hχΩ hχ1
    (rev409_isCutoffDatum_zero 0 χ) ?_ ?_
  · funext i ψ
    simp [restrictDatum, restrictField]
  · rw [rev409_zeroExtension_zero]
    simp [tsupport, Function.support]
