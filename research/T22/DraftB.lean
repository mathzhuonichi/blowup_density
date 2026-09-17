import Contracts.V1.Data

/-!
Independent T22 draft B: `03-torus.tex:600-631`.
Statements and definitions only; no inhabitant of the API is asserted.
The whole-space carrier, angular realization, physical-field bridge and norm
are imported verbatim from D01. No torus norm is needed by these displays.
All new definitions below need registration / to be aligned with T10.
-/

noncomputable section
namespace BlowupDensity.Research.T22.DraftB

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-- `03-torus.tex:601-604`: compactly supported smooth tests inside Ω,
represented as Schwartz functions on R³. Needs registration / to be aligned with T10. -/
abbrev DomainTest (Ω : Set Space) :=
  {ψ : SchwartzMap Space ℂ // HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω}

/-- `03-torus.tex:601-606`: coordinates of a restricted distribution.
Only elements with a Sobolev extension have finite norm below; arbitrary
functionals are permitted as a total ambient type, not assumed to be distributions.
Needs registration / to be aligned with T10. -/
abbrev DomainFunctional (Ω : Set Space) := Fin 3 → DomainTest Ω → ℂ

/-- `03-torus.tex:601-604`: distributional restriction of the registered
whole-space datum, including negative orders.
Needs registration / to be aligned with T10. -/
def restrictDatum (Ω : Set Space) (s : ℝ) (A : RealVectorSobolev s) :
    DomainFunctional Ω :=
  fun i ψ => angularRealization s ((A i : FourierData)) ψ.1

/-- `03-torus.tex:603-606`, eq:restriction-norm, literally the infimum over
all distributional extensions, not merely function-valued extensions.
An empty extension family has norm ∞. Finite-domain Sobolev elements are
those functionals in the image of `restrictDatum`.
Needs registration / to be aligned with T10. -/
def domainSobolevENorm (Ω : Set Space) (s : ℝ) (z : DomainFunctional Ω) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // restrictDatum Ω s A = z}, ‖A.1‖ₑ

/-- `03-torus.tex:608-615`: a locally smooth physical field restricted to Ω,
paired only against compact interior tests. Values outside Ω are ignored.
Needs registration / to be aligned with T10. -/
def restrictField (Ω : Set Space) (z : SpatialField) : DomainFunctional Ω :=
  fun i ψ => ∫ x in Ω, ψ.1 x * ((z x i : ℝ) : ℂ)

/-- `03-torus.tex:615`: literal extension by zero of the values on Ω.
Needs registration / to be aligned with T10. -/
def zeroExtension (Ω : Set Space) (z : SpatialField) : SpatialField :=
  Ω.indicator z

/-- `03-torus.tex:617-618`: multiplication of a distribution by a fixed smooth
real cutoff, using the transpose action on Schwartz tests (no conjugation).
Smooth compact cutoffs have temperate growth, so `smulLeftCLM` is pointwise
multiplication in every application below.
Needs registration / to be aligned with T10. -/
def IsCutoffDatum (s : ℝ) (χ : Space → ℝ)
    (A B : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((B i : FourierData)) ψ =
      angularRealization s ((A i : FourierData))
        (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) ψ)

/-- `03-torus.tex:603-631`: bounded-domain norm statements. The quotient-norm
identity itself is the definition `domainSobolevENorm`, rather than a redundant
API field. Ω is any open set (in particular an open bounded box or smooth
domain); no boundary regularity is needed for these local statements. -/
structure BoundedDomainNormAPI : Prop where
  /-- `03-torus.tex:606-607`: order zero is the ordinary domain L² norm.
  Local smoothness ensures the distributional pairing is meaningful; no global
  integrability is imposed, and both sides may be infinite. -/
  orderZero : ∀ (Ω : Set Space), IsOpen Ω → ∀ z : SpatialField,
    ContDiffOn ℝ ∞ z Ω →
    domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω)

  /-- `03-torus.tex:617-624`: every fixed compact smooth cutoff is an H^s
  multiplier for every real order. C depends on s and χ, never on A. -/
  cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ

  /-- `03-torus.tex:608-626`, eq:zero-extension. The single constant is chosen
  before z: it is uniform over every smaller support and every ε-family in K.
  Using the support of the zero extension allows arbitrary values outside Ω.
  Smoothness is required only inside Ω; K is compactly contained there. -/
  zeroExtensionComparison : ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
    ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
      ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
      domainSobolevENorm Ω s (restrictField Ω z) ≤
          sobolevENorm s (zeroExtension Ω z) ∧
      sobolevENorm s (zeroExtension Ω z) ≤
          ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z)

end BlowupDensity.Research.T22.DraftB
