import Tests.Localization

/-!
# `T02.localization` conformance and transitive-axiom audit

Run from `verification/` with
`lake env lean ../research/T13/axioms_contract.lean`.
Every proof declaration below is expected to use only
`[propext, Classical.choice, Quot.sound]`.
-/

open BlowupDensity.Bindings

#print axioms fundamentalCube_eq
#print axioms supportedInBall_eq
#print axioms localization_latticeVector_eq
#print axioms periodize_eq
#print axioms fractionalRadialKernel_eq
#print axioms cFrac_eq
#print axioms periodicKernel_eq
#print axioms latticeTail_eq
#print axioms IReal_eq
#print axioms ITorus_eq
#print axioms gradientENorm_eq
#print axioms localization_dotHomogeneousENorm_eq
#print axioms localizationAPI
#print axioms BlowupDensity.Tests.checkedLocalization

/-- The audited theorem is the registered six-field declaration, transported
from the concrete canonical record rather than assumed as a hypothesis. -/
example : BlowupDensity.Contracts.V1.LocalizationAPI :=
  BlowupDensity.Tests.checkedLocalization
