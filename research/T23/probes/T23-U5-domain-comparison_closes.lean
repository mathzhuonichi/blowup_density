import NSFormalization.Section3.T23.DomainComparison
import Contracts.V1.BoundedDomainNorm

/-!
# T23 U5 closure probe

The examples below check the five copied T23 norm definitions, fieldwise
transport of the registered/canonical T22 API, the order-zero interpretation,
and the exact `BoundaryInsertionAPI.domain_zeroExt_comparison` target from the
threaded U3/U4 fields.
-/

noncomputable section

namespace NSFormalization.Section3.T23.DomainComparisonProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T22
open scoped ContDiff ENNReal

namespace Registered

abbrev API := BlowupDensity.Contracts.V1.BoundedDomainNorm.BoundedDomainNormAPI

set_option linter.defProp false in
def toCanonical (D : API) : BoundedDomainNormAPI :=
  ⟨D.orderZero, D.cutoffMultiplier, D.zeroExtensionComparison⟩

set_option linter.defProp false in
def ofCanonical (D : BoundedDomainNormAPI) : API :=
  ⟨D.orderZero, D.cutoffMultiplier, D.zeroExtensionComparison⟩

example (D : BoundedDomainNormAPI) : toCanonical (ofCanonical D) = D := by
  exact rfl

example (D : API) : ofCanonical (toCanonical D) = D := by
  exact rfl

example :
    BlowupDensity.Contracts.V1.BoundedDomainNorm.domainSobolevENorm =
      domainSobolevENorm := by
  exact rfl

example :
    BlowupDensity.Contracts.V1.BoundedDomainNorm.restrictField =
      restrictField := by
  exact rfl

example :
    BlowupDensity.Contracts.V1.BoundedDomainNorm.zeroExtension =
      zeroExtension := by
  exact rfl

end Registered

example (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) :
    domainEnergyEssSup Ω T z =
      essSup (fun t ↦ eLpNorm (fun x ↦ z (t, x)) 2 (volume.restrict Ω))
        (volume.restrict (Ioo (0 : ℝ) T)) := by
  exact domainEnergyEssSup_eq Ω T z

example (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) :
    domainEnergyGradient Ω T z =
      (∫⁻ t in Ioo (0 : ℝ) T,
          (eLpNorm (fun x ↦ NSFormalization.Section4.I02.spatialGradient z t x)
            2 (volume.restrict Ω)) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
  exact domainEnergyGradient_eq Ω T z

example (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) :
    domainEnergyENorm Ω T z =
      domainEnergyEssSup Ω T z + domainEnergyGradient Ω T z := by
  exact domainEnergyENorm_eq Ω T z

example (Ω : Set Space) (s : ℝ) (f : SpaceTimeField) :
    domainForceSobolevENorm Ω s f =
      ∫⁻ t in Ioi (0 : ℝ),
        domainSobolevENorm Ω s (restrictField Ω (fun x ↦ f (t, x))) := by
  exact domainForceSobolevENorm_eq Ω s f

example (Ω : Set Space) (s : ℝ) (f : SpaceTimeField) :
    zeroExtForceSobolevENorm Ω s f =
      ∫⁻ t in Ioi (0 : ℝ),
        NSFormalization.Section4.D01.sobolevENorm s
          (zeroExtension Ω (fun x ↦ f (t, x))) := by
  exact zeroExtForceSobolevENorm_eq Ω s f

variable {u : NavierStokes.ProblemStatement.VelocityField}
  {p : NavierStokes.ProblemStatement.PressureField}
  {f : NavierStokes.ProblemStatement.VelocityField}
  {K : Set Space} {place : DomainPlacementData u p f K}
  {Ω : Set Space} {ε₀ : ℝ} {force : ℝ → SpaceTimeField} {g : SpaceTimeField}

example (norms : BoundedDomainNormAPI)
    (hΩ : IsOpen Ω)
    (hforce : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (fun z ↦ force ε z - g z) ∈ forceClassOmega Ω) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioi (0 : ℝ),
      domainSobolevENorm Ω 0
          (restrictField Ω (fun x ↦ force ε (t, x) - g (t, x))) =
        eLpNorm (fun x ↦ force ε (t, x) - g (t, x)) 2
          (volume.restrict Ω) := by
  exact domainForceDifference_orderZero norms hΩ hforce

/-- Exact U5 field, instantiated only from the canonical domain geometry,
U3 force-class membership, and U4 fixed all-time support. -/
example (norms : BoundedDomainNormAPI)
    (hdomain : IsBoundedBoxOrSmoothDomain Ω)
    (hinterior :
      closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω)
    (hforce : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (fun z ↦ force ε z - g z) ∈ forceClassOmega Ω)
    (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ∀ t : ℝ, ∀ x : Space, force ε (t, x) - g (t, x) ≠ 0 →
        x ∈ closure (Metric.ball place.chartCenter place.chartRadius)) :
    ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        domainForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ≤
            zeroExtForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ∧
        zeroExtForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ≤
            ENNReal.ofReal C *
              domainForceSobolevENorm Ω s (fun z ↦ force ε z - g z) := by
  exact domain_zeroExt_comparison norms hdomain.1 place.chartRadius_pos
    hinterior hforce hsupport

end NSFormalization.Section3.T23.DomainComparisonProbe
