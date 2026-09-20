import Contracts.V1.Data

/-!
# T22 reconciled specification: bounded-domain restriction and zero extension

This is the statement-only reconciliation selected by
`research/T22/RECONCILIATION.md` for `paper/sections/03-torus.tex:600-630`,
especially `eq:restriction-norm` at lines 603-605 and `eq:zero-extension` at
lines 610-614.  It keeps Draft B's distributional quotient definition and its
three-field propositional API, with Draft A's citation detail folded into the
documentation.

## Vocabulary choice

The whole-space carrier, angular realization, physical-field bridge, and norm
are reused directly from the registered `Contracts.V1.Data` vocabulary:
`SpatialField`, `RealVectorSobolev`, `angularRealization`, `FourierData`, and
`sobolevENorm`.  No definition is copied from `research/T10/Spec.lean`.
That file is a standalone research specification and cannot be imported as a
module; more importantly, the binding ruling in `research/T22/RECONCILIATION.md`
§3 says that T22's two displays are entirely on `R^3` and `Omega` and require
no periodic T10 object.  The later T23 consumer, rather than this norm layer,
is where the registered version of T10's periodic vocabulary will meet these
definitions.

All definitions introduced here still need registration.  No inhabitant of
`BoundedDomainNormAPI` is asserted, and no bounded zero-extension operator on
arbitrary `H^s(Omega)` is encoded.
-/

noncomputable section

namespace BlowupDensity.T22.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## Bounded-domain distributional vocabulary -/

/-- `03-torus.tex:601-604`: compactly supported smooth tests inside `Omega`,
represented as Schwartz functions on `R^3`.

This definition needs registration. -/
abbrev DomainTest (Ω : Set Space) :=
  {ψ : SchwartzMap Space ℂ // HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω}

/-- `03-torus.tex:601-606`: coordinates of a distribution restricted to
`Omega`.  Only functionals admitting a Sobolev extension have finite norm
below; the ambient type itself is deliberately total.

This definition needs registration. -/
abbrev DomainFunctional (Ω : Set Space) := Fin 3 → DomainTest Ω → ℂ

/-- `03-torus.tex:601-604`: distributional restriction of a registered
whole-space datum, including at negative orders.

This definition needs registration. -/
def restrictDatum (Ω : Set Space) (s : ℝ) (A : RealVectorSobolev s) :
    DomainFunctional Ω :=
  fun i ψ => angularRealization s ((A i : FourierData)) ψ.1

/-- `03-torus.tex:603-606`, `eq:restriction-norm`: the quotient extended norm,
literally the infimum over all distributional `H^s(R^3)` extensions.  An empty
extension family has value `top`, so the definition remains fail-safe at every
real order, including negative orders.

This definition needs registration. -/
def domainSobolevENorm (Ω : Set Space) (s : ℝ)
    (z : DomainFunctional Ω) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // restrictDatum Ω s A = z}, ‖A.1‖ₑ

/-- `03-torus.tex:608-615`: a locally smooth physical field restricted to
`Omega`, paired only against compactly supported interior tests.  Values
outside `Omega` do not contribute.

This definition needs registration. -/
def restrictField (Ω : Set Space) (z : SpatialField) : DomainFunctional Ω :=
  fun i ψ => ∫ x in Ω, ψ.1 x * ((z x i : ℝ) : ℂ)

/-- `03-torus.tex:610-615`: literal extension by zero of the values on
`Omega`.  Values supplied by the ambient representative outside `Omega` are
ignored.

This definition needs registration. -/
def zeroExtension (Ω : Set Space) (z : SpatialField) : SpatialField :=
  Ω.indicator z

/-- `03-torus.tex:616-624`: `B` is the product of a whole-space Sobolev datum
`A` by the fixed real cutoff `chi`, expressed through the transpose action on
Schwartz tests.  No conjugation is inserted.

For the smooth compact cutoffs quantified in `cutoffMultiplier`,
`SchwartzMap.smulLeftCLM` is ordinary pointwise multiplication.  This graph
definition needs registration. -/
def IsCutoffDatum (s : ℝ) (χ : Space → ℝ)
    (A B : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((B i : FourierData)) ψ =
      angularRealization s ((A i : FourierData))
        (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) ψ)

/-! ## Reconciled target API -/

/-- The three bounded-domain norm facts selected by
`research/T22/RECONCILIATION.md` for `03-torus.tex:600-630`.

The quotient-norm identity is the definition `domainSobolevENorm`, rather than
a redundant API field.  `Omega` is any open set; boundedness and boundary
regularity are not used by these local statements. -/
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

end BlowupDensity.T22.Draft
