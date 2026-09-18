import Contracts.V1.BoundedDomainNorm
import NSFormalization.Section3.T22.Assembly

/-!
# Binding for the T22 bounded-domain norm contract

The contract repeats only the bounded-domain definitions from the reconciled
specification.  Each repeat is guarded below by a whole-definition `rfl`
bridge; the API witness is then the canonical Section 3 assembly.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

namespace BoundedDomainNorm

theorem domainTest_eq :
    Contracts.V1.BoundedDomainNorm.DomainTest =
      NSFormalization.Section3.T22.DomainTest := rfl

theorem domainFunctional_eq :
    Contracts.V1.BoundedDomainNorm.DomainFunctional =
      NSFormalization.Section3.T22.DomainFunctional := rfl

theorem restrictDatum_eq :
    Contracts.V1.BoundedDomainNorm.restrictDatum =
      NSFormalization.Section3.T22.restrictDatum := rfl

theorem domainSobolevENorm_eq :
    Contracts.V1.BoundedDomainNorm.domainSobolevENorm =
      NSFormalization.Section3.T22.domainSobolevENorm := rfl

theorem restrictField_eq :
    Contracts.V1.BoundedDomainNorm.restrictField =
      NSFormalization.Section3.T22.restrictField := rfl

theorem zeroExtension_eq :
    Contracts.V1.BoundedDomainNorm.zeroExtension =
      NSFormalization.Section3.T22.zeroExtension := rfl

theorem isCutoffDatum_eq :
    Contracts.V1.BoundedDomainNorm.IsCutoffDatum =
      NSFormalization.Section3.T22.IsCutoffDatum := rfl

/- The two `BoundedDomainNormAPI` records are separate inductive types (the
   contract cannot import the proof-side record), so their existential aliases
   are transported fieldwise rather than by `rfl`. -/
def toCanonical
    (D : Contracts.V1.BoundedDomainNorm.BoundedDomainNormAPI) :
    NSFormalization.Section3.T22.BoundedDomainNormAPI :=
  ⟨D.orderZero, D.cutoffMultiplier, D.zeroExtensionComparison⟩

def ofCanonical
    (D : NSFormalization.Section3.T22.BoundedDomainNormAPI) :
    Contracts.V1.BoundedDomainNorm.BoundedDomainNormAPI :=
  ⟨D.orderZero, D.cutoffMultiplier, D.zeroExtensionComparison⟩

theorem ofCanonical_toCanonical (D : NSFormalization.Section3.T22.BoundedDomainNormAPI) :
    toCanonical (ofCanonical D) = D := rfl

theorem toCanonical_ofCanonical
    (D : Contracts.V1.BoundedDomainNorm.BoundedDomainNormAPI) :
    ofCanonical (toCanonical D) = D := rfl

theorem boundedDomainNormStatement_iff :
    Contracts.V1.BoundedDomainNorm.boundedDomainNormStatement ↔
      NSFormalization.Section3.T22.boundedDomainNormStatement := by
  constructor
  · rintro ⟨D⟩
    exact ⟨toCanonical D⟩
  · rintro ⟨D⟩
    exact ⟨ofCanonical D⟩

/-- The canonical three-field witness transported into the contract namespace. -/
def boundedDomainNorm : Contracts.V1.BoundedDomainNorm.BoundedDomainNormAPI := {
  orderZero := NSFormalization.Section3.T22.boundedDomainNorm.orderZero
  cutoffMultiplier := NSFormalization.Section3.T22.boundedDomainNorm.cutoffMultiplier
  zeroExtensionComparison :=
    NSFormalization.Section3.T22.boundedDomainNorm.zeroExtensionComparison
}

theorem boundedDomainNormStatement_holds :
    Contracts.V1.BoundedDomainNorm.boundedDomainNormStatement :=
  ⟨boundedDomainNorm⟩

end BoundedDomainNorm

end BlowupDensity.Bindings
