import Contracts.V1.Thresholds
import NSFormalization.Paper3.Thresholds

/-! The only layer that knows the current implementation's names and paths. -/

noncomputable section
namespace BlowupDensity.Bindings

/-- Bind existing arithmetic lemmas to the stable version-one contract. -/
def thresholds : Contracts.V1.ThresholdAPI where
  exponent := NSFormalization.Paper3.forceExponent
  formula := fun _ _ => rfl
  positive := NSFormalization.Paper3.forceExponent_pos_iff
  l1 := NSFormalization.Paper3.forceExponent_one
  l2 := NSFormalization.Paper3.forceExponent_two
  negativeIndex := fun _ hs => NSFormalization.Paper3.negative_intermediate_index hs
  energy := NSFormalization.Paper3.energy_force_exponents

end BlowupDensity.Bindings
