import Contracts.V4.EnergyAbsorption
import Bindings.EnergyAbsorptionV4
import TestSupport.Axioms

noncomputable section
namespace BlowupDensity.Tests
open Set MeasureTheory
open Contracts.V1.Data
open Contracts.V1 (laplacian)
open Contracts.V1.EnergyAbsorptionPartial
open Contracts.V2.EnergyAbsorptionPartial
open Contracts.V3.EnergyAbsorptionPartial
open scoped ENNReal

def checkedEnergyAbsorptionV4 : Contracts.V4.EnergyAbsorption.EnergyAbsorptionAPI :=
  Bindings.energyAbsorptionV4

run_cmd TestSupport.checkAxioms ``checkedEnergyAbsorptionV4
run_cmd TestSupport.checkAxioms ``Bindings.energyAbsorptionPartialV3_of_v4

example : checkedEnergyAbsorptionV4.toEnergyAbsorptionPartialV3API =
    Bindings.energyAbsorptionPartialV3 := Bindings.energyAbsorptionPartialV3_of_v4

/-! Six exact field shapes, independently consumed from the checked witness. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => gradientSq (slice w.velocity s))
            (2 * advectionWork (slice w.velocity t) -
              2 * ν * laplacianSq (slice w.velocity t) -
              2 * pairing (slice f t) (laplacian (slice w.velocity t))) t :=
  checkedEnergyAbsorptionV4.enstrophyIdentity

example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ENNReal.ofReal checkedEnergyAbsorptionV4.C₁ * criticalL3 (slice w.velocity t) ≤
              ENNReal.ofReal (ν / 4) →
            ∀ E' : ℝ, HasDerivAt (fun s => gradientSq (slice w.velocity s)) E' t →
              E' + ν * laplacianSq (slice w.velocity t) ≤
                checkedEnergyAbsorptionV4.CRH1 * ν⁻¹ * l2Sq (slice f t) :=
  checkedEnergyAbsorptionV4.enstrophyDifferentialBound

example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          (∀ s ∈ Ico (0 : ℝ) t, ENNReal.ofReal checkedEnergyAbsorptionV4.C₁ * criticalL3 (slice w.velocity s) ≤
              ENNReal.ofReal (ν / 4)) →
            IntervalIntegrable (fun s => laplacianSq (slice w.velocity s)) volume 0 t ∧
              gradientSq (slice w.velocity t) +
                  ν * ∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s) ≤
                gradientSq a + checkedEnergyAbsorptionV4.CRH1 * ν⁻¹ * ∫ s in (0 : ℝ)..t, l2Sq (slice f s) :=
  checkedEnergyAbsorptionV4.enstrophyIntegralBound

example :
    ∀ z : SpatialField, MemHInfty z →
      sobolevENorm 2 z ^ (2 : ℝ) ≤
        ENNReal.ofReal (checkedEnergyAbsorptionV4.CH2 * (l2Sq z + laplacianSq z)) :=
  checkedEnergyAbsorptionV4.sobolevTwoFourier

example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T) (S : ℝ), 0 < S → S ≤ T →
          (∀ t ∈ Ico (0 : ℝ) S, ENNReal.ofReal checkedEnergyAbsorptionV4.C₁ * criticalL3 (slice w.velocity t) ≤
              ENNReal.ofReal (ν / 4)) →
            ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
              ENNReal.ofReal
                (checkedEnergyAbsorptionV4.Cassembly * S * energyBudget a f S ^ 2 +
                  checkedEnergyAbsorptionV4.Cassembly * ν⁻¹ * gradientSq a +
                  checkedEnergyAbsorptionV4.Cassembly * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s)) :=
  checkedEnergyAbsorptionV4.h2TimeIntegral

example :
    ∀ (ν : ℝ), 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      ∀ (T : ℝ) (w : ClassicalSolutionR ν (fun _ => 0) f T) (S : ℝ), 0 < S → S ≤ T →
        (∀ t ∈ Ico (0 : ℝ) S, ENNReal.ofReal checkedEnergyAbsorptionV4.C₁ * criticalL3 (slice w.velocity t) ≤
            ENNReal.ofReal (ν / 4)) →
          ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
            ENNReal.ofReal
              (checkedEnergyAbsorptionV4.Cassembly * S * forcePrimitive f S ^ 2 +
                checkedEnergyAbsorptionV4.Cassembly * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s)) :=
  checkedEnergyAbsorptionV4.h2TimeIntegralZeroDatum

/-- The possibly singular terminal horizon is admitted, with genuine finiteness. -/
theorem energyAbsorptionV4_terminalFinite
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassR)
    (f : SpaceTimeField) (hf : MemForceR f) (T : ℝ) (w : ClassicalSolutionR ν a f T)
    (hsmall : ∀ t ∈ Ico (0 : ℝ) T,
      ENNReal.ofReal checkedEnergyAbsorptionV4.C₁ * criticalL3 (slice w.velocity t) ≤
        ENNReal.ofReal (ν / 4)) :
    (∫⁻ t in Ioo (0 : ℝ) T, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ)) < ⊤ := by
  exact lt_of_le_of_lt
    (checkedEnergyAbsorptionV4.h2TimeIntegral ν hν a ha f hf T w T
      w.horizon_pos le_rfl hsmall) ENNReal.ofReal_lt_top

run_cmd TestSupport.checkAxioms ``energyAbsorptionV4_terminalFinite

end BlowupDensity.Tests
