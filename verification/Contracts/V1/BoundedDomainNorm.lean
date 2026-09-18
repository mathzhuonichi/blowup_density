import Contracts.V1.Data

/-!
# T22 bounded-domain restriction and zero extension

This contract is the registered copy of `research/T22/Spec.lean`.  The
whole-space carrier, angular realization, physical-field bridge, and norm use
the already registered `Contracts.V1.Data` vocabulary; the bounded-domain
definitions are restated here because contracts cannot import the proof-side
`NSFormalization.Section3.T22` module.  The corresponding `rfl` bridges live in
`Bindings.BoundedDomainNorm`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.BoundedDomainNorm

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## Bounded-domain distributional vocabulary -/

/- Provenance: `research/T22/Spec.lean:48-50`; restated verbatim. -/
abbrev DomainTest (Ω : Set Space) :=
  {ψ : SchwartzMap Space ℂ // HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω}

/- Provenance: `research/T22/Spec.lean:56`; restated verbatim. -/
abbrev DomainFunctional (Ω : Set Space) := Fin 3 → DomainTest Ω → ℂ

/- Provenance: `research/T22/Spec.lean:65-67`; restated verbatim. -/
def restrictDatum (Ω : Set Space) (s : ℝ) (A : RealVectorSobolev s) :
    DomainFunctional Ω :=
  fun i ψ => angularRealization s ((A i : FourierData)) ψ.1

/- Provenance: `research/T22/Spec.lean:74-76`; restated verbatim. -/
def domainSobolevENorm (Ω : Set Space) (s : ℝ)
    (z : DomainFunctional Ω) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // restrictDatum Ω s A = z}, ‖A.1‖ₑ

/- Provenance: `research/T22/Spec.lean:83-85`; restated verbatim. -/
def restrictField (Ω : Set Space) (z : SpatialField) : DomainFunctional Ω :=
  fun i ψ => ∫ x in Ω, ψ.1 x * ((z x i : ℝ) : ℂ)

/- Provenance: `research/T22/Spec.lean:92-94`; restated verbatim. -/
def zeroExtension (Ω : Set Space) (z : SpatialField) : SpatialField :=
  Ω.indicator z

/- Provenance: `research/T22/Spec.lean:103-107`; restated verbatim. -/
def IsCutoffDatum (s : ℝ) (χ : Space → ℝ)
    (A B : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((B i : FourierData)) ψ =
      angularRealization s ((A i : FourierData))
        (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) ψ)

/-! ## Reconciled target API -/

/- Provenance: `research/T22/Spec.lean:114-167`; copied token-for-token. -/
structure BoundedDomainNormAPI : Prop where
  /-- `03-torus.tex:606-607`: at order zero the restriction quotient norm is
  the usual vector `L^2(Omega)` norm.  Local smoothness makes the displayed
  physical pairing meaningful; either side is allowed to be infinite.

  Exact quantifier order: `forall Omega`, openness, `forall z`, then
  smoothness on `Omega`.

  Non-vacuity: this equates the independently defined distributional infimum
  with the concrete restricted-measure `eLpNorm`; it is not an unfolding of
  `domainSobolevENorm`. -/
  orderZero : ∀ (Ω : Set Space), IsOpen Ω → ∀ z : SpatialField,
    ContDiffOn ℝ ∞ z Ω →
    domainSobolevENorm Ω 0 (restrictField Ω z) =
      eLpNorm z 2 (volume.restrict Ω)

  /-- `03-torus.tex:616-624`: multiplication by a fixed compactly supported
  smooth cutoff is bounded on `H^s(R^3)` for every real `s`.  The finite
  positive constant depends only on `s` and `chi`, and is chosen before `A`.

  Exact quantifier order: `forall s chi`, regularity of `chi`, `exists C > 0`,
  `forall A`, then `exists B` realizing the cutoff product.

  Non-vacuity: the conclusion produces an actual datum `B`, pins its
  distributional graph by `IsCutoffDatum`, and bounds its concrete extended
  norm uniformly over all input data. -/
  cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ

  /-- `03-torus.tex:608-626`, `eq:zero-extension`: for a fixed compact
  `K` contained in an open `Omega`, every real Sobolev order has one positive
  constant giving the displayed two-sided comparison for all smooth fields
  whose zero extension is supported in `K`.

  Exact quantifier order: `forall Omega K`, the geometric hypotheses,
  `forall s`, `exists C > 0`, and only then `forall z`.  Thus `C` is uniform
  over smaller supports, time slices, and shrinking `epsilon`-families that
  stay inside the same `K`, as required at `03-torus.tex:626-629`.

  Non-vacuity: the conclusion is the full chain between the domain quotient
  norm and the registered whole-space norm of the literal zero extension.
  Its interior-support hypothesis deliberately prevents this field from
  asserting a bounded zero-extension operator on arbitrary domain data. -/
  zeroExtensionComparison :
      ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
        ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
          ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
          domainSobolevENorm Ω s (restrictField Ω z) ≤
              sobolevENorm s (zeroExtension Ω z) ∧
          sobolevENorm s (zeroExtension Ω z) ≤
              ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z)

/- Provenance: `research/T22/Spec.lean` statement form requested by U-REG. -/
def boundedDomainNormStatement : Prop := Nonempty BoundedDomainNormAPI

end BlowupDensity.Contracts.V1.BoundedDomainNorm
