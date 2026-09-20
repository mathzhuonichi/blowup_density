import Contracts.V1.CompletedDensity
import Bindings.CompletedSobolevDensity
import Bindings.CompletedClosure
import Bindings.ScalingHomogeneousClosed

/-! The complete Proposition 4.6 witness, assembling lanes 256 and 259 and
discharging lane 259's sole realization input with lane 255. -/

noncomputable section

namespace BlowupDensity.Bindings

/-- All three clauses of Proposition 4.6 in the registered vocabulary. -/
theorem completedDensity :
    Contracts.V1.CompletedDensity.CompletedDensityAPI :=
  { completedSobolevDensity := completedSobolevDensity
    completedHomogeneousDensity := completedHomogeneousDensity_of_realization
      NSFormalization.Section4.I03.compactHomogeneousRealization
    strongTrajectoryClosure := strongTrajectoryClosure_of_realization
      NSFormalization.Section4.I03.compactHomogeneousRealization }

end BlowupDensity.Bindings
