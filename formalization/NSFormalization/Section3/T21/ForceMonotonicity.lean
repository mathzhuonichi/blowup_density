import NSFormalization.Section3.T21.Definitions
import NSFormalization.Section3.T15.Convergence

/-!
# T21 N3: force Sobolev monotonicity

T15 already transports every admissible measurable Sobolev path through the
continuous order-lowering multiplier.  The T21 field is its specialization to
time exponent one and lower order `1 / 2`.
-/

noncomputable section

namespace NSFormalization.Section3.T21

open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10

/-- N3: the exact force-norm monotonicity field. -/
theorem forceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ f : SpaceTimeField,
    forceSobolevENormT 1 (1 / 2) f ≤ forceSobolevENormT 1 s f := by
  intro s hs f
  exact NSFormalization.Section3.T15.forceSobolevENormT_mono_order hs f

end NSFormalization.Section3.T21
