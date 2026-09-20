import NSFormalization.Section3.T11.MildClassical

/-! Negative reviewer probe: widen the headline affine conclusion from `Ico`
to `Icc`.  This is intentionally false as a direct consequence: the lane
only supplies the path on the half-open lifespan, so `simpa` must fail rather
than silently dropping a hypothesis. -/
noncomputable section
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T11

example {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (c : Space) :
    ∃ w : ClassicalSolutionT ν (fun _ ↦ c) (fun _ : SpaceTime ↦ c) 1,
      PeriodicLocalRegularity  ν (fun _ ↦ c) (fun _ : SpaceTime ↦ c) 1 w ∧
      IsPeriodicSobolevPathOn 3 (Icc 0 1) w.velocity
        (fun t ↦ (1 + t) • torusConstantDatum 3 c) := by
  simpa using
    (mild_to_classical_affine_constant hν C 1 one_pos c)
