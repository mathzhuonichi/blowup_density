import Tests.CriticalRegularity

open MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

/-! Reviewer probe: the strict smallness premise is inhabited at zero force. -/

example (ν : ℝ) (hν : 0 < ν) :
    maximalLifespanR ν (fun _ => 0) (0 : SpaceTimeField) = ⊤ := by
  apply BlowupDensity.Tests.checkedCriticalRegularity.inhomogeneousAtZero ν hν 0
    NSFormalization.Section4.A04.memForceR_zero
  have hz : forceSobolevENormL1 (1 / 2) (0 : SpaceTimeField) = 0 := by
    apply le_antisymm _ bot_le
    apply iInf_le_of_le ⟨fun _ => 0,
      (fun _ _ => NSFormalization.Section4.D01.isSobolevDatum_zero _),
      aestronglyMeasurable_zero⟩
    simp [bochnerDatumENorm]
  rw [hz]
  exact ENNReal.ofReal_pos.mpr
    (mul_pos BlowupDensity.Tests.checkedCriticalRegularity.hc hν)

/-! The general field's strict premise is inhabited at zero datum and force too. -/
example (ν : ℝ) (hν : 0 < ν) :
    maximalLifespanR ν (0 : SpatialField) (0 : SpaceTimeField) = ⊤ := by
  apply BlowupDensity.Tests.checkedCriticalRegularity.universal ν hν 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0
    NSFormalization.Section4.A04.memForceR_zero
  have hdot : dotHomogeneousENorm (1 / 2) (0 : SpatialField) = 0 :=
    NSFormalization.Section4.D01.dotHomogeneousENorm_zero _
  have hsob : forceSobolevENormL1 (1 / 2) (0 : SpaceTimeField) = 0 := by
    apply le_antisymm _ bot_le
    apply iInf_le_of_le ⟨fun _ => 0,
      (fun _ _ => NSFormalization.Section4.D01.isSobolevDatum_zero _),
      aestronglyMeasurable_zero⟩
    simp [bochnerDatumENorm]
  have hhom : forceHomogeneousENorm 1 (1 / 2) (0 : SpaceTimeField) = 0 := by
    apply le_antisymm _ bot_le
    exact (NSFormalization.Section4.R43.forceHomogeneousENorm_le_forceSobolevENormL1
      0 NSFormalization.Section4.A04.memForceR_zero).trans_eq hsob
  rw [hdot, hhom, zero_add]
  exact ENNReal.ofReal_pos.mpr
    (mul_pos BlowupDensity.Tests.checkedCriticalRegularity.hc hν)
