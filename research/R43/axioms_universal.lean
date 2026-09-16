import NSFormalization.Section4.R43.Universal
import Bindings.MaximalPartial

open NSFormalization.Section4
open NSFormalization.Section4.A02
open NSFormalization.Section4.R43
open MeasureTheory
open scoped ENNReal

#print axioms NSFormalization.Section4.R43.critical_norm_bound_general
#print axioms NSFormalization.Section4.R43.critical_bootstrap_general
#print axioms NSFormalization.Section4.R43.critical_initial_add_prefix_le
#print axioms NSFormalization.Section4.R43.criticalNormAt_le_general
#print axioms NSFormalization.Section4.R43.critical_absorption_general
#print axioms NSFormalization.Section4.R43.maximal_critical_absorption_general
#print axioms NSFormalization.Section4.R43.maximal_h2TimeIntegral_general
#print axioms NSFormalization.Section4.R43.maximal_squaredHTwoIntegral_general
#print axioms NSFormalization.Section4.R43.universal_of_memForceR

/-- The zero-datum specialization recovers lane 223 with the same constant. -/
theorem universal_recovers_endpoint :
    ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      D01.forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν) →
        maximalLifespanR ν (fun _ => 0) f = ⊤ := by
  intro ν hν f hf hs
  apply universal_of_memForceR ν hν 0 zero_mem_initialClassR f hf
  rw [D01.dotHomogeneousENorm_zero, zero_add]
  exact (forceHomogeneousENorm_le_forceSobolevENormL1 f hf).trans_lt hs

#print axioms universal_recovers_endpoint

example (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField) (hf : MemForceR f)
    (hs : D01.forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν)) :
    maximalLifespanR ν (fun _ => 0) f = ⊤ :=
  universal_recovers_endpoint ν hν f hf hs

example (ν : ℝ) (hν : 0 < ν) :
    maximalLifespanR ν (fun _ => 0) (0 : SpaceTimeField) = ⊤ := by
  apply universal_recovers_endpoint ν hν 0 A04.memForceR_zero
  have hz : D01.forceSobolevENormL1 (1 / 2) (0 : SpaceTimeField) = 0 := by
    apply le_antisymm _ bot_le
    apply iInf_le_of_le ⟨fun _ => 0, (fun _ _ => D01.isSobolevDatum_zero _),
      aestronglyMeasurable_zero⟩
    simp [D01.Homogeneous.bochnerDatumENorm]
  rw [hz]
  exact ENNReal.ofReal_pos.mpr (mul_pos criticalConst_pos hν)

noncomputable section
namespace UniversalConformance
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)

-- The spec's physical-field datum infimum, copied verbatim.
def dotHomogeneousENorm (s : ℝ) (z : BlowupDensity.Contracts.V1.Data.SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

theorem dotHomogeneousENorm_eq : dotHomogeneousENorm = D01.dotHomogeneousENorm := rfl

theorem universal :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : BlowupDensity.Contracts.V1.Data.SpatialField,
        a ∈ BlowupDensity.Contracts.V1.Data.initialClassR →
        ∀ f : BlowupDensity.Contracts.V1.Data.SpaceTimeField,
          BlowupDensity.Contracts.V1.Data.MemForceR f →
          dotHomogeneousENorm (1 / 2) a +
            BlowupDensity.Contracts.V1.Data.forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (criticalConst * ν) →
            BlowupDensity.Contracts.V1.Data.maximalLifespanR ν a f = ⊤ := by
  intro ν hν a ha f hf hs
  rw [← BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq]
  exact universal_of_memForceR ν hν a ha f hf hs

#print axioms dotHomogeneousENorm
#print axioms dotHomogeneousENorm_eq
#print axioms universal
end UniversalConformance
