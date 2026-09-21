import NSFormalization.Section3.T11.Rescaling

noncomputable section

namespace NSFormalization.Section3.T11.Review314

open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T11

/- The first restore viscosity is deliberately changed from `ν` to `-ν`.
The original proof must not establish this mutated identity. -/
example : ∀ (ν : ℝ), 0 < ν → ∀ (u : SpaceTimeField),
    restoreViscosityVelocityT (-ν) (unitViscosityVelocityT ν u) = u := by
  intro ν hν u
  have hν0 : ν ≠ 0 := ne_of_gt hν
  funext z
  simp [restoreViscosityVelocityT, unitViscosityVelocityT, smul_smul, hν0]

end NSFormalization.Section3.T11.Review314
