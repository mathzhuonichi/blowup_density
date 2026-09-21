import Contracts.V1.EnergyHighPartial
import Bindings.EnergyHighPartial
import Tests.EnergyHighPartial

/-!
# A04 `energy_high_partial` contract conformance (lane 133)

Axiom audit for the binding and the checked test declaration, plus a conformance
`example` written in the **contract's own vocabulary**
(`Contracts.V1.EnergyHighPartial.{sobolevNormAt, gradientSobolevNormAt,
HasSmoothSobolevPath}`, `Contracts.V1.Data.{ClassicalSolutionR, initialClassR,
MemForceR}`, and the API's `Chigh`), discharged by the binding field.  Elaboration
succeeding is proof that `Bindings.energyHighPartial.energyIdentityHigh` has exactly
the frozen field's shape.

`lake env lean` from `verification/`; the `#print axioms` lines below must each show
only `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
open Set
open BlowupDensity.Contracts.V1.Data

#print axioms BlowupDensity.Bindings.energyHighPartial
#print axioms BlowupDensity.Tests.checkedEnergyHighPartial
#print axioms BlowupDensity.Bindings.energyHighPartial_Chigh_eq_Ctame
#print axioms BlowupDensity.Bindings.energyHighPartial_gradientSobolevENorm_velocity_ne_top

/-- Conformance: the frozen field `energyIdentityHigh`, in the contract's own
vocabulary, is inhabited by the binding. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ w : ClassicalSolutionR ν a f T,
        BlowupDensity.Contracts.V1.EnergyHighPartial.HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T,
            ∃ d : ℝ,
              HasDerivAt (fun r : ℝ =>
                BlowupDensity.Contracts.V1.EnergyHighPartial.sobolevNormAt (m : ℝ)
                  w.velocity r ^ 2) d t ∧
                (1 / 2) * d +
                    ν * BlowupDensity.Contracts.V1.EnergyHighPartial.gradientSobolevNormAt
                        (m : ℝ) w.velocity t ^ 2 ≤
                  BlowupDensity.Bindings.energyHighPartial.Chigh m *
                      BlowupDensity.Contracts.V1.EnergyHighPartial.sobolevNormAt 2 w.velocity t *
                      BlowupDensity.Contracts.V1.EnergyHighPartial.sobolevNormAt (m : ℝ)
                        w.velocity t *
                      BlowupDensity.Contracts.V1.EnergyHighPartial.gradientSobolevNormAt (m : ℝ)
                        w.velocity t +
                    BlowupDensity.Contracts.V1.EnergyHighPartial.sobolevNormAt (m : ℝ) f t *
                      BlowupDensity.Contracts.V1.EnergyHighPartial.sobolevNormAt (m : ℝ)
                        w.velocity t :=
  BlowupDensity.Bindings.energyHighPartial.energyIdentityHigh
