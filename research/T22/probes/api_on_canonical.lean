import Contracts.V1.Data
import NSFormalization.Section3.T22.Domain

/-! Definitional drift probe for the T22 canonical vocabulary. -/

noncomputable section

namespace BlowupDensity.T22.Probe

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

example : DomainTest = NSFormalization.Section3.T22.DomainTest := rfl
example : DomainFunctional = NSFormalization.Section3.T22.DomainFunctional := rfl
example : restrictDatum = NSFormalization.Section3.T22.restrictDatum := rfl
example : domainSobolevENorm = NSFormalization.Section3.T22.domainSobolevENorm := rfl
example : restrictField = NSFormalization.Section3.T22.restrictField := rfl
example : zeroExtension = NSFormalization.Section3.T22.zeroExtension := rfl
example : IsCutoffDatum = NSFormalization.Section3.T22.IsCutoffDatum := rfl

theorem BoundedDomainNormAPI.toCanonical
    (D : BoundedDomainNormAPI) : NSFormalization.Section3.T22.BoundedDomainNormAPI :=
  { orderZero := D.orderZero
    cutoffMultiplier := D.cutoffMultiplier
    zeroExtensionComparison := D.zeroExtensionComparison }

theorem BoundedDomainNormAPI.ofCanonical
    (D : NSFormalization.Section3.T22.BoundedDomainNormAPI) : BoundedDomainNormAPI :=
  { orderZero := D.orderZero
    cutoffMultiplier := D.cutoffMultiplier
    zeroExtensionComparison := D.zeroExtensionComparison }

example (D : BoundedDomainNormAPI) :
    BoundedDomainNormAPI.ofCanonical D.toCanonical = D := by
  cases D
  rfl

example (D : NSFormalization.Section3.T22.BoundedDomainNormAPI) :
    BoundedDomainNormAPI.toCanonical (BoundedDomainNormAPI.ofCanonical D) = D := by
  cases D
  rfl

#print axioms DomainTest
#print axioms DomainFunctional
#print axioms restrictDatum
#print axioms domainSobolevENorm
#print axioms restrictField
#print axioms zeroExtension
#print axioms IsCutoffDatum
#print axioms BoundedDomainNormAPI
#print axioms BoundedDomainNormAPI.toCanonical
#print axioms BoundedDomainNormAPI.ofCanonical

end BlowupDensity.T22.Probe
