import Tests.TorusData

noncomputable section

namespace Review293

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Bindings
open scoped ENNReal

/-- The amended datum and `L²` hypotheses are simultaneously satisfiable on
the concrete zero physical field, and forward Parseval then applies. -/
example :
    ∃ A : PeriodicSobolev 0,
      IsPeriodicDatum 0 (0 : SpatialField) A ∧
        MemLp (torusLift (0 : SpatialField)) 2 periodicTorusMeasure ∧
        ‖A‖ₑ = eLpNorm (torusLift (0 : SpatialField)) 2 periodicTorusMeasure := by
  have hp : IsPeriodicSpatial (0 : SpatialField) := by
    intro x i
    rfl
  have hL2 : MemLp (torusLift (0 : SpatialField)) 2 periodicTorusMeasure :=
    MemLp.zero
  obtain ⟨A, hA⟩ := torusData.parseval_backward (0 : SpatialField) hp hL2
  exact ⟨A, hA, hL2, torusData.parseval_forward (0 : SpatialField) A hA hL2⟩

end Review293
