import NSFormalization.Section3.T21.MainAssembly

/-! Reviewer non-vacuity probes at concrete positive parameters. -/

noncomputable section

namespace NSFormalization.Section3.T21.ReviewerNonvacuity

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T20 (criticalSmallnessH1)
open NSFormalization.Section4.A02 (SpaceTimeField)

/-- The critical ball used to prove non-density is inhabited at `ν = s = 1`. -/
example : (0 : SpaceTimeField) ∈ criticalBallT criticalSmallnessH1 1 1 :=
  closedNonDensityAPI.zeroMemBall 1 zero_lt_one 1

/-- The zero-datum breakdown set is inhabited at `ν = T = 1`, obtained from
the proved subcritical density assertion rather than an assumed witness. -/
example : ∃ f : SpaceTimeField, f ∈ breakdownSetTZero 1 1 := by
  have hdense : RelativelyDenseT 1 0 forceClassT (breakdownSetTZero 1 1) :=
    closedMainTheoremAPI.fixedInitialDensity
      (fun _ : Space ↦ 0) closedMainTheoremAPI.zeroInitialClass
      1 zero_lt_one 1 zero_lt_one 0 (by norm_num)
  obtain ⟨f, hf, _hclose⟩ := hdense (0 : SpaceTimeField) zero_mem_forceClassT
    1 zero_lt_one
  exact ⟨f, hf⟩

end NSFormalization.Section3.T21.ReviewerNonvacuity
