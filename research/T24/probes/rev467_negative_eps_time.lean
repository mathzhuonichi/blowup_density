import NSFormalization.Section3.T24.MultipleComponents

noncomputable section
namespace Rev467NegativeEpsTime

open NSFormalization.Section3.T24
open NavierStokes.ProblemStatement

variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ}

/-- Deliberate mutation: flip the main `eps_time` inequality. The original proof
term must not elaborate at this strengthened, mathematically opposite target. -/
example (d : RegionsData ν u p f K M E) : ∀ j, d.T < d.ε j ^ 2 := by
  intro j
  exact d.eps_time j

end Rev467NegativeEpsTime
