import NSFormalization.Section3.T24.MultipleAssembled

noncomputable section
namespace NSFormalization.Section3.T24.Rev468Mutation

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10

variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData ν u p f K M E)

/-- Deliberately false strengthening for the review: widen the momentum
equation from the open interval `(0,T)` to the half-open interval `[0,T)`.
The actual proof must not elaborate against this mutated statement. -/
theorem momentum_widened_mutation : ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν d.assembledVelocity
      d.assembledPressure t x = d.assembledForce (t, x) := by
  exact d.assembled_momentum

end NSFormalization.Section3.T24.Rev468Mutation
