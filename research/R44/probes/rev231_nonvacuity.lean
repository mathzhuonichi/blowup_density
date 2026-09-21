import Tests.CriticalFiniteHorizon

open MeasureTheory
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! Reviewer probe: zero force inhabits the registered strict smallness ball. -/

example (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S) :
    ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) (0 : SpaceTimeField) := by
  apply BlowupDensity.Tests.checkedCriticalFiniteHorizon.main ν S hν hS 0
    NSFormalization.Section4.A04.memForceR_zero
  have hz : forceSobolevENormL2 (-1 / 2) (0 : SpaceTimeField) = 0 := by
    apply le_antisymm _ bot_le
    apply iInf_le_of_le ⟨fun _ => 0,
      (fun _ _ => NSFormalization.Section4.D01.isSobolevDatum_zero _),
      aestronglyMeasurable_zero⟩
    simp [bochnerDatumENorm]
  rw [hz]
  exact ENNReal.ofReal_pos.mpr
    (BlowupDensity.Tests.checkedCriticalFiniteHorizon.radiusPos ν S hν hS)
