import NSFormalization.Section3.T24.AffineEnergy

namespace NSFormalization.Section3.T24.Rev407Mutation

open Set
open NavierStokes.ProblemStatement

/- A substantive mutation of Ua6: change the energy time from 1 to 2.
   The delivered theorem cannot close this changed statement from its 1-time
   hypothesis; the expected type mismatch is recorded in REVIEW_407. -/
example {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (henergy : energyENorm 1 U < ⊤) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      energyENorm 2 (affineVelocity U b) < ⊤ := by
  exact energy_finite c r τ₀ τ₁ henergy

end NSFormalization.Section3.T24.Rev407Mutation
