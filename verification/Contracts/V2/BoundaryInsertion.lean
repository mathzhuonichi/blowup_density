import Contracts.V1.BoundaryInsertion

/-! The bounded-domain insertion statement with no extra integration-by-parts
premise. The version-one mathematical vocabulary and all 48 conclusion fields
are retained. The compatible correction and cutoff are chosen existentially;
the theorem does not quantify over an arbitrary prescribed cutoff. -/
namespace BlowupDensity.Contracts.V2.BoundaryInsertion

/-- The strong box-or-smooth-domain statement, without the V1 `IBP` premise. -/
def boundaryInsertionStatementV2 : Prop :=
  V1.BoundaryInsertion.boundaryInsertionStatement'

end BlowupDensity.Contracts.V2.BoundaryInsertion
