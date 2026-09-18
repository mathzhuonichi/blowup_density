import NSFormalization.Section3.T11.CriterionBridge

noncomputable section
namespace NSFormalization.Section3.T11.ReviewerNonvacuity

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal

/-- The constant-field witness used below is genuinely nonzero. -/
example : (coordinateVector 0 : Space) ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Space ↦ v (0 : Fin 3)) h
  simp [coordinateVector] at h0

/-- A concrete nonzero smooth periodic field has finite extended norm at every
real Sobolev order. -/
example (s : ℝ) :
    periodicSobolevENorm s (fun _ ↦ coordinateVector 0) ≠ ⊤ := by
  exact periodicSobolevENorm_ne_top_smooth s contDiff_const (fun _ _ ↦ rfl)

end NSFormalization.Section3.T11.ReviewerNonvacuity
