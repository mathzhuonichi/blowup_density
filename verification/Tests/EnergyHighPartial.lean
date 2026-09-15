import Contracts.V1.EnergyHighPartial
import Bindings.EnergyHighPartial
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

open Set

/-- An implementation must supply every field of the unchanged specification. -/
def checkedEnergyHighPartial :
    Contracts.V1.EnergyHighPartial.EnergyHighPartialAPI :=
  Bindings.energyHighPartial

run_cmd TestSupport.checkAxioms ``checkedEnergyHighPartial

/-- The frozen field, in the manuscript's shape
(`paper/sections/appendix-a-local-theory.tex:132-137`):
`½ (d/dt)‖u‖²_{H^m} + ν‖∇u‖²_{H^m} ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}`. -/
example :
    ∀ (ν : ℝ) (a : Contracts.V1.Data.SpatialField) (f : Contracts.V1.Data.SpaceTimeField)
      (T : ℝ), 0 < ν → a ∈ Contracts.V1.Data.initialClassR → Contracts.V1.Data.MemForceR f →
        ∀ w : Contracts.V1.Data.ClassicalSolutionR ν a f T,
          Contracts.V1.EnergyHighPartial.HasSmoothSobolevPath T w.velocity →
            ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T,
              ∃ d : ℝ,
                HasDerivAt
                  (fun r : ℝ =>
                    Contracts.V1.EnergyHighPartial.sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
                  (1 / 2) * d +
                      ν * Contracts.V1.EnergyHighPartial.gradientSobolevNormAt (m : ℝ)
                          w.velocity t ^ 2 ≤
                    checkedEnergyHighPartial.Chigh m *
                        Contracts.V1.EnergyHighPartial.sobolevNormAt 2 w.velocity t *
                        Contracts.V1.EnergyHighPartial.sobolevNormAt (m : ℝ) w.velocity t *
                        Contracts.V1.EnergyHighPartial.gradientSobolevNormAt (m : ℝ)
                          w.velocity t +
                      Contracts.V1.EnergyHighPartial.sobolevNormAt (m : ℝ) f t *
                        Contracts.V1.EnergyHighPartial.sobolevNormAt (m : ℝ) w.velocity t :=
  checkedEnergyHighPartial.energyIdentityHigh

/-- The constant is strictly positive at every order. -/
example : ∀ m : ℕ, 0 < checkedEnergyHighPartial.Chigh m :=
  checkedEnergyHighPartial.Chigh_pos

end BlowupDensity.Tests
