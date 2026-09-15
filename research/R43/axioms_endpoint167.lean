import NSFormalization.Section4.R43.MaximalEndpoint
import Bindings.MaximalPartialV2
import Bindings.EnergyAbsorptionV4

noncomputable section

namespace BlowupDensity.R43.Endpoint167

open Set MeasureTheory
open Contracts.V1.Data
open Contracts.V1.EnergyAbsorptionPartial
open Contracts.V2.EnergyAbsorptionPartial
open Contracts.V3.EnergyAbsorptionPartial
open scoped ENNReal

/-- Consumer of the actual frozen maximal-family predicate, on the original
data and fields. The bound includes equality with a finite maximal lifespan. -/
theorem frozen_maximal_h2TimeIntegral {ν S : ℝ} {a : SpatialField}
    {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (hu : Contracts.V2.MaximalPartial.IsMaximalSolution ν a f u p)
    (hS : 0 < S) (hSL : ENNReal.ofReal S ≤ maximalLifespanR ν a f)
    (hsmall : ∀ t ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal Bindings.energyAbsorptionV4.C₁ * criticalL3 (slice u t) ≤
        ENNReal.ofReal (ν / 4)) :
    ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice u t) ^ (2 : ℝ) ≤
      ENNReal.ofReal (32 * S * energyBudget a f S ^ 2 +
        32 * ν⁻¹ * gradientSq a +
        32 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s)) := by
  have hmax := (Bindings.maximalPartial_isMaximalSolution_iff ν a f u p).mpr hu
  have hbound : ENNReal.ofReal S ≤ NSFormalization.Section4.A02.maximalLifespanR ν a f := by
    simpa only [Bindings.maximalPartial_maximalLifespanR_eq] using hSL
  simp only [Bindings.energyAbsorptionPartialV2_gradientSq_eq]
  exact NSFormalization.Section4.R43.maximal_h2TimeIntegral hν ha hf hmax hS hbound hsmall

theorem frozen_maximal_squaredHTwoIntegral_ne_top {ν S : ℝ} {a : SpatialField}
    {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (hu : Contracts.V2.MaximalPartial.IsMaximalSolution ν a f u p)
    (hS : 0 < S) (hSL : ENNReal.ofReal S ≤ maximalLifespanR ν a f)
    (hsmall : ∀ t ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal Bindings.energyAbsorptionV4.C₁ * criticalL3 (slice u t) ≤
        ENNReal.ofReal (ν / 4)) :
    NSFormalization.Section4.A04.squaredHTwoIntegral S u ≠ ⊤ := by
  apply NSFormalization.Section4.R43.maximal_squaredHTwoIntegral_ne_top hν ha hf
    ((Bindings.maximalPartial_isMaximalSolution_iff ν a f u p).mpr hu) hS
  · simpa only [Bindings.maximalPartial_maximalLifespanR_eq] using hSL
  · exact hsmall

#print axioms NSFormalization.Section4.R43.maximal_h2TimeIntegral
#print axioms NSFormalization.Section4.R43.maximal_squaredHTwoIntegral_ne_top
#print axioms frozen_maximal_h2TimeIntegral
#print axioms frozen_maximal_squaredHTwoIntegral_ne_top

end BlowupDensity.R43.Endpoint167
