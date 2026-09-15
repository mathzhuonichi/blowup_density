import Bindings.EnergyAbsorptionPartialV3
import NSFormalization.Section4.C01.H2TimeIntegral

noncomputable section

open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial
  (slice l2Sq laplacianSq criticalL3)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq)
open BlowupDensity.Contracts.V3.EnergyAbsorptionPartial (energyBudget forcePrimitive)
open BlowupDensity.Bindings
open scoped ENNReal

namespace C01H2Conformance164

theorem gradient_bridge : gradientSq = NSFormalization.Section4.C01.gradientSq := by
  funext z
  exact energyAbsorptionPartialV2_gradientSq_eq z

/-- Original Spec field with explicit CH2=16. -/
theorem sobolevTwoFourier : ∀ z : SpatialField, MemHInfty z →
    sobolevENorm 2 z ^ (2 : ℝ) ≤ ENNReal.ofReal (16 * (l2Sq z + laplacianSq z)) :=
  NSFormalization.Section4.C01.sobolevTwoFourier

/-- Original Spec field with explicit Cassembly=32 and the registered C1.
The hypothesis is S≤T, not S<T. -/
theorem h2TimeIntegral :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T) (S : ℝ), 0 < S → S ≤ T →
          (∀ t ∈ Ico (0 : ℝ) S, ENNReal.ofReal energyAbsorptionPartialV3.C₁ *
            criticalL3 (slice w.velocity t) ≤ ENNReal.ofReal (ν / 4)) →
            ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
              ENNReal.ofReal (32 * S * energyBudget a f S ^ 2 +
                32 * ν⁻¹ * gradientSq a +
                32 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s)) := by
  intro ν hν a _ f hf T w S hS hST hsmall
  rw [gradient_bridge]
  exact NSFormalization.Section4.C01.h2TimeIntegral hν (uniqueness_toA02 w) hf hS hST hsmall

/-- Original zero-datum Spec field, with the same Cassembly. -/
theorem h2TimeIntegralZeroDatum :
    ∀ (ν : ℝ), 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      ∀ (T : ℝ) (w : ClassicalSolutionR ν (fun _ => 0) f T) (S : ℝ), 0 < S → S ≤ T →
        (∀ t ∈ Ico (0 : ℝ) S, ENNReal.ofReal energyAbsorptionPartialV3.C₁ *
          criticalL3 (slice w.velocity t) ≤ ENNReal.ofReal (ν / 4)) →
          ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
            ENNReal.ofReal (32 * S * forcePrimitive f S ^ 2 +
              32 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s)) := by
  intro ν hν f hf T w S hS hST hsmall
  exact NSFormalization.Section4.C01.h2TimeIntegralZeroDatum hν
    (uniqueness_toA02 w) hf hS hST hsmall

/-- The terminal endpoint is actually consumable and gives a finite bound. -/
theorem terminal_finite {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) (hT : 0 < T)
    (hsmall : ∀ t ∈ Ico (0 : ℝ) T,
      ENNReal.ofReal energyAbsorptionPartialV3.C₁ * criticalL3 (slice w.velocity t) ≤
        ENNReal.ofReal (ν / 4)) :
    (∫⁻ t in Ioo (0 : ℝ) T, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ)) < ⊤ :=
  lt_of_le_of_lt (h2TimeIntegral ν hν a ha f hf T w T hT le_rfl hsmall)
    ENNReal.ofReal_lt_top

end C01H2Conformance164

#print axioms C01H2Conformance164.sobolevTwoFourier
#print axioms C01H2Conformance164.h2TimeIntegral
#print axioms C01H2Conformance164.h2TimeIntegralZeroDatum
#print axioms C01H2Conformance164.terminal_finite
#print axioms NSFormalization.Section4.C01.weakDerivsL2Bound_two
#print axioms NSFormalization.Section4.C01.lintegral_Ioo_le_of_Ioc
