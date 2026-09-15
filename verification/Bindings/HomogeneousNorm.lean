import Contracts.V1.HomogeneousNorm
import NSFormalization.Section4.D01.HomogeneousNorm

/-! The definitional bridge from the self-contained G1 contract to its implementation. -/

noncomputable section

namespace BlowupDensity.Bindings

/-- The contract and implementation use the same datum-infimum definition.
This `rfl` theorem is the drift guard required for a contract-side restatement. -/
theorem dotHomogeneousENorm_eq :
    Contracts.V1.HomogeneousNorm.dotHomogeneousENorm =
      NSFormalization.Section4.D01.dotHomogeneousENorm := rfl

end BlowupDensity.Bindings
