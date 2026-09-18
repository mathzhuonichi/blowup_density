import NSFormalization.Section4.D01.SmoothDatum
import NSFormalization.Section4.A02.SolutionClass

/-!
# T22 bounded-domain vocabulary

This is the canonical Section 3 realization of the reconciled T22
specification.  The whole-space carrier and Sobolev datum vocabulary are
imported from Section 4 D01; the declarations below are only the bounded
domain layer.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal SchwartzMap

/-- Compactly supported smooth tests contained in the domain. -/
abbrev DomainTest (Ω : Set Space) :=
  {ψ : SchwartzMap Space ℂ // HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω}

/-- The total carrier of vector-valued distributions on domain tests. -/
abbrev DomainFunctional (Ω : Set Space) := Fin 3 → DomainTest Ω → ℂ

/-- Distributional restriction of a whole-space Sobolev datum. -/
def restrictDatum (Ω : Set Space) (s : ℝ) (A : RealVectorSobolev s) :
    DomainFunctional Ω :=
  fun i ψ => angularRealization s ((A i : FourierData)) ψ.1

/-- The quotient extended norm over all whole-space Sobolev extensions. -/
def domainSobolevENorm (Ω : Set Space) (s : ℝ)
    (z : DomainFunctional Ω) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // restrictDatum Ω s A = z}, ‖A.1‖ₑ

/-- The distributional restriction of a physical field to compact interior tests. -/
def restrictField (Ω : Set Space) (z : SpatialField) : DomainFunctional Ω :=
  fun i ψ => ∫ x in Ω, ψ.1 x * ((z x i : ℝ) : ℂ)

/-- Literal extension by zero on the domain. -/
def zeroExtension (Ω : Set Space) (z : SpatialField) : SpatialField :=
  Ω.indicator z

/-- The transpose graph of multiplication by a real cutoff. -/
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

end NSFormalization.Section3.T22
