import Tests.TorusData

noncomputable section

namespace Review296

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Bindings
open scoped ENNReal

/-- The datum and physical `L²` hypotheses are jointly inhabited by the zero
field, and both directions of Parseval apply to the resulting datum. -/
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

end Review296
