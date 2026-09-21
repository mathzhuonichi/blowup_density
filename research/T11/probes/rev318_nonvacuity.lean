import NSFormalization.Section3.T11.PhysicalRecovery

noncomputable section
namespace NSFormalization.Section3.T11.Rev318Nonvacuity

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10

-- Both the initial velocity and the force use the nonzero first coordinate vector.
example : ∃ (C : TorusTwoSpaceContract 1) (T : ℝ) (u : ℝ → PeriodicSobolev 3),
    0 < T ∧
      TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
        (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) T u ∧
      torusConstantDatum 3 (coordinateVector 0) ≠ 0 ∧
      torusPhysicalVelocity u (0, 0) ≠ 0 ∧
      torusPhysicalField (torusConstantDatum 3 (coordinateVector 0)) 0 ≠ 0 := by
  obtain ⟨C, T, u, hT, hu, _, hv, hf⟩ := torusPhysicalRecovery_nonzero
  have hforce : torusConstantDatum 3 (coordinateVector 0) ≠ 0 := by
    intro h
    have hc := congrArg
      (fun A : PeriodicSobolev 3 ↦ A.1 0 (0 : PeriodicFrequency)) h
    norm_num [torusConstantDatum, coordinateVector] at hc
  exact ⟨C, T, u, hT, hu, hforce, hv, hf⟩

end NSFormalization.Section3.T11.Rev318Nonvacuity
