import Tests.TorusData

noncomputable section

namespace Review296

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Bindings
open scoped ENNReal

/-- Substantive mutation: multiply the physical norm by `2`, retaining every
binder and hypothesis of the registered forward Parseval field. -/
example :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = 2 * eLpNorm (torusLift z) 2 periodicTorusMeasure := by
  intro z A hA hz
  exact torusData.parseval_forward z A hA hz

end Review296
