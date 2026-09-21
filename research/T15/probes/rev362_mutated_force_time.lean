import NSFormalization.Section3.T15.Bridges

noncomputable section

open NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Source.PacketScaling
open NSFormalization.Section3.T15

/- This deliberately changes the rescaling start time from `T - ε ^ 2` to
`T + ε ^ 2`.  The `rfl` proof must fail. -/
example (f : VelocityField) (x₀ : Space) (T ε : ℝ) :
    scaledForce f x₀ T ε =
      parabolicForce ε⁻¹ (T + ε ^ 2) x₀ f := by
  rfl
