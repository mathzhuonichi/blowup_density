import Bindings.InsertionFromData
import NSFormalization.Section4.A04.ZeroSolution

open BlowupDensity BlowupDensity.Bindings
open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open scoped ENNReal

#print axioms insertionFromData_packet
#print axioms insertionLifespanV2_of_data
#print axioms insertionFromData_lifespan
#print axioms insertionFromData_forceConvergence

namespace BlowupDensity.Bindings.InsertionFromDataAudit

/-- A concrete admissible instance: viscosity one, zero datum/force, time one.
The horizon-two zero solution supplies the strict lifespan hypothesis. -/
theorem zero_instance :
    ∃ (P : PacketAPI 1)
      (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API 1 P),
      L.family.a = 0 ∧ L.family.g = 0 ∧ L.family.T = 1 := by
  apply insertionLifespanV2_of_data 1 zero_lt_one 1 zero_lt_one 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0
    NSFormalization.Section4.A04.memForceR_zero
  apply (maximalPartial.regularThrough_iff 1 0 0 1 zero_lt_one).mp
  exact ⟨1, zero_lt_one, ⟨maximalPartial_ofA02
    (NSFormalization.Section4.A04.zeroSol 1 (1 + 1) zero_lt_one (by norm_num))⟩⟩

#print axioms zero_instance

/-- The concrete output has a nonempty parameter range and actual lifespan one. -/
theorem zero_inserted_lifespan :
    ∃ (P : PacketAPI 1)
      (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API 1 P) (ε : ℝ),
      ε ∈ Set.Ioc (0 : ℝ) L.family.ε₀ ∧
      maximalLifespanR 1 0 (L.family.force ε) = ENNReal.ofReal 1 := by
  obtain ⟨P, L, ha, _, hT⟩ := zero_instance
  exact ⟨P, L, L.family.ε₀, ⟨L.family.eps_pos, le_rfl⟩,
    insertionFromData_lifespan L ha hT _ ⟨L.family.eps_pos, le_rfl⟩⟩

#print axioms zero_inserted_lifespan

end BlowupDensity.Bindings.InsertionFromDataAudit
