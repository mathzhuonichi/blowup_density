import Contracts.V1.MultipleRegions

noncomputable section
namespace Rev471WrongDissipationConstant

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal BigOperators

/- Deliberate substantive mutation of the main conclusion: replace the exact
packet constant `D^2` by `D^2 + 1`.  The delivered field must not elaborate at
this different dissipation identity. -/
example {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : MultipleRegionsAPI P T c r) :
    (energyGradientT T a.assembled_velocity) ^ (2 : ℕ) =
      ENNReal.ofReal ((P.dissipationBound ^ 2 + 1) * ∑ j : Fin N, a.ε j) := by
  exact a.dissipation_bound

end Rev471WrongDissipationConstant
