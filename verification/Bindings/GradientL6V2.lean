import Contracts.V2.GradientL6
import Bindings.GradientL6
import Bindings.HomogeneousNorm
import NSFormalization.Section4.A05.CriticalL3

/-!
The implementation binding for A05's version-two critical embedding.

The implementation theorem states its hypothesis with
`NSFormalization.Section4.A02.MemHInfty`; the contract uses
`Contracts.V1.Data.MemHInfty`.  Both predicates are the same conjunction
(`ContDiff` plus integer-order datum existence) and are definitionally equal,
as the explicit bridge below records.

The implementation's local homogeneous norm predates D01's registered name.
The second bridge below composes the two drift guards

`A05.dotHomogeneousENorm = D01.dotHomogeneousENorm
  = Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`.
-/

noncomputable section

namespace BlowupDensity.Bindings

open MeasureTheory
open scoped ENNReal

/-- The implementation's A02 hypothesis and the frozen contract hypothesis are
definitionally equal; neither is stronger. -/
theorem gradientL6V2_memHInfty_eq (v : Contracts.V1.Data.SpatialField) :
    Contracts.V1.Data.MemHInfty v =
      NSFormalization.Section4.A02.MemHInfty v := rfl

/-- Lane 165's local norm and D01's canonical implementation norm have the
identical datum-infimum body (`REVIEW_165-A05-critical-l3.md`, "canonical norm:
rfl"). -/
theorem gradientL6V2_A05_dotHomogeneousENorm_eq :
    NSFormalization.Section4.A05.dotHomogeneousENorm =
      NSFormalization.Section4.D01.dotHomogeneousENorm := rfl

/-- The complete bridge from lane 165's local spelling, through D01's canonical
implementation name, to the registered contract definition. -/
theorem gradientL6V2_dotHomogeneousENorm_eq :
    NSFormalization.Section4.A05.dotHomogeneousENorm =
      Contracts.V1.HomogeneousNorm.dotHomogeneousENorm := by
  calc
    NSFormalization.Section4.A05.dotHomogeneousENorm =
        NSFormalization.Section4.D01.dotHomogeneousENorm :=
      gradientL6V2_A05_dotHomogeneousENorm_eq
    _ = Contracts.V1.HomogeneousNorm.dotHomogeneousENorm :=
      dotHomogeneousENorm_eq.symm

/-- The constant family selected for the focused V2 interface.  Only the
order-half value occurs in its single new field. -/
def gradientL6V2Constant : ℝ → ℝ :=
  fun _ => NSFormalization.Section4.A05.criticalL3Const

/-- Bind the frozen V1 record plus lane 165's proved critical `L³` theorem. -/
def gradientL6V2 : Contracts.V2.GradientL6V2API gradientL6V2Constant :=
  { gradientL6 with
    velocityCriticalL3 := fun v hv => by
      change eLpNorm v 3 volume ≤
        ENNReal.ofReal NSFormalization.Section4.A05.criticalL3Const *
          NSFormalization.Section4.A05.dotHomogeneousENorm (1 / 2) v
      exact NSFormalization.Section4.A05.velocityCriticalL3 v hv }

/-- The new constant is positive.  Positivity is a binding-level fact because
the focused contract imports only the one requested Spec field, not `C_pos`. -/
theorem gradientL6V2Constant_pos (a : ℝ) : 0 < gradientL6V2Constant a :=
  NSFormalization.Section4.A05.criticalL3Const_pos

/-- Version one is recovered definitionally, with its frozen witness unchanged. -/
theorem gradientL6_of_v2 :
    gradientL6V2.toGradientL6API = gradientL6 := rfl

end BlowupDensity.Bindings
