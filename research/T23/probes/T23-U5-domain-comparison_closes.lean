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

/-! The historical T22 block from `research/T23/Spec.lean:205-333` is repeated
in its original namespace only inside this standalone probe, so its separate
inductive record can be transported fieldwise to the canonical proof-side
record.  Production code never imports or restates it. -/
namespace BlowupDensity.T22.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

abbrev DomainTest (Ω : Set Space) :=
  {ψ : SchwartzMap Space ℂ // HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω}

abbrev DomainFunctional (Ω : Set Space) := Fin 3 → DomainTest Ω → ℂ

def restrictDatum (Ω : Set Space) (s : ℝ) (A : RealVectorSobolev s) :
    DomainFunctional Ω :=
  fun i ψ => angularRealization s ((A i : FourierData)) ψ.1

def domainSobolevENorm (Ω : Set Space) (s : ℝ)
    (z : DomainFunctional Ω) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // restrictDatum Ω s A = z}, ‖A.1‖ₑ

def restrictField (Ω : Set Space) (z : SpatialField) : DomainFunctional Ω :=
  fun i ψ => ∫ x in Ω, ψ.1 x * ((z x i : ℝ) : ℂ)

def zeroExtension (Ω : Set Space) (z : SpatialField) : SpatialField :=
  Ω.indicator z

def IsCutoffDatum (s : ℝ) (χ : Space → ℝ)
    (A B : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((B i : FourierData)) ψ =
      angularRealization s ((A i : FourierData))
        (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) ψ)

structure BoundedDomainNormAPI : Prop where
  orderZero : ∀ (Ω : Set Space), IsOpen Ω → ∀ z : SpatialField,
    ContDiffOn ℝ ∞ z Ω →
    domainSobolevENorm Ω 0 (restrictField Ω z) =
      eLpNorm z 2 (volume.restrict Ω)
  cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ
  zeroExtensionComparison :
      ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
        ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
          ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
          domainSobolevENorm Ω s (restrictField Ω z) ≤
              sobolevENorm s (zeroExtension Ω z) ∧
          sobolevENorm s (zeroExtension Ω z) ≤
              ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z)

end BlowupDensity.T22.Draft

namespace NSFormalization.Section3.T23.DomainComparisonProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T22
open scoped ContDiff ENNReal

namespace Historical

abbrev API := BlowupDensity.T22.Draft.BoundedDomainNormAPI

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

example : BlowupDensity.T22.Draft.restrictDatum = restrictDatum := by
  exact rfl

example : BlowupDensity.T22.Draft.domainSobolevENorm = domainSobolevENorm := by
  exact rfl

example : BlowupDensity.T22.Draft.restrictField = restrictField := by
  exact rfl

example : BlowupDensity.T22.Draft.zeroExtension = zeroExtension := by
  exact rfl

example : BlowupDensity.T22.Draft.IsCutoffDatum = IsCutoffDatum := by
  exact rfl

end Historical

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
