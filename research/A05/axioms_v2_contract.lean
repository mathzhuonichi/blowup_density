import Tests.GradientL6V2

/-! Permanent conformance and transitive-axiom audit for lane 181. -/

noncomputable section

namespace Lane181A05V2Audit

open MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

/-- The registered witness has the exact `Spec.lean:366-368` field shape. -/
example :
    ∀ v : SpatialField, MemHInfty v →
      eLpNorm v 3 volume ≤
        ENNReal.ofReal (BlowupDensity.Bindings.gradientL6V2Constant (1 / 2)) *
          dotHomogeneousENorm (1 / 2) v :=
  BlowupDensity.Tests.checkedGradientL6V2.velocityCriticalL3

/-- The chosen universal constant is genuinely positive. -/
example : 0 < BlowupDensity.Bindings.gradientL6V2Constant (1 / 2) :=
  BlowupDensity.Bindings.gradientL6V2Constant_pos _

#print axioms NSFormalization.Section4.A05.velocityCriticalL3
#print axioms BlowupDensity.Bindings.gradientL6V2_memHInfty_eq
#print axioms BlowupDensity.Bindings.gradientL6V2_A05_dotHomogeneousENorm_eq
#print axioms BlowupDensity.Bindings.gradientL6V2_dotHomogeneousENorm_eq
#print axioms BlowupDensity.Bindings.gradientL6V2Constant_pos
#print axioms BlowupDensity.Bindings.gradientL6V2
#print axioms BlowupDensity.Bindings.gradientL6_of_v2
#print axioms BlowupDensity.Tests.checkedGradientL6V2

end Lane181A05V2Audit
