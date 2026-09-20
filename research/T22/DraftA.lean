import Contracts.V1.Data

/-!
# T22 draft A: bounded-domain restriction and zero-extension norms

Double-blind statement draft for `collaboration/tasks/T22.md`.  The target is
`paper/sections/03-torus.tex:600-630`, especially `eq:restriction-norm` at
`:603-605` and `eq:zero-extension` at `:610-614`.

The whole-space side is reused verbatim from `Contracts.V1.Data`:
`SpatialField`, `RealVectorSobolev`, `IsSobolevDatum`, and `sobolevENorm` use the
paper's angular Fourier convention and Euclidean `PiLp 2` vector norm.  The
bounded-domain quotient objects below are local to this draft.

## Needs registration / to be aligned with T10

`zeroExtension`, `HasIntegrableSchwartzPairings`, `SobolevExtension`,
`restrictionSobolevENorm`, `domainL2ENorm`, `cutoffProduct`,
`IsBoundedOpenDomain`, `CompactlyContained`, and `IsSmoothSupportedIn` need
registration.  Before registration their physical-field aliases should be
aligned with T10's periodic physical layer (which the Section 3 plan requires
to remain a field on `R^3`).  No coefficient-side torus norm is duplicated
here: T22 only consumes the already registered whole-space datum and adds the
bounded-domain quotient.

`SobolevExtension` carries a datum rather than merely asking that
`sobolevENorm s Z < top`.  This is necessary because `Data.IsSobolevDatum` uses
a totalized Schwartz pairing; its documented caveat becomes reachable if the
quotient infimum ranges over completely arbitrary representatives.  The
explicit `HasIntegrableSchwartzPairings` field excludes exactly that pathology
and is automatic for genuine `H^s(R^3)` representatives.

The constant `C Omega K s` and cutoff `chi Omega K` in
`BoundedDomainNormAPI` are selected before the field (or any shrinking scale)
is quantified.  Thus `zero_extension` has the paper's required uniformity:
one constant works for every smaller support contained in the fixed `K`, hence
for every member of an epsilon-indexed concentrating family.

No bounded zero-extension operator on arbitrary `H^s(Omega)` is asserted, in
accord with `paper/sections/03-torus.tex:629-630`.
-/

noncomputable section

namespace BlowupDensity.Research.T22.DraftA

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## Spec-local bounded-domain objects -/

/-- `paper/sections/03-torus.tex:610-615`: extension by zero from `Omega` to
`R^3`.  The input remains an ambient `SpatialField`; values outside `Omega` are
ignored.  This lets T23 use the repository's physical-field type without
introducing a second function carrier for a domain restriction.

**Needs registration / to be aligned with T10's physical-field alias.** -/
def zeroExtension (Ω : Set Space) (z : SpatialField) : SpatialField := by
  classical
  exact fun x => if x ∈ Ω then z x else 0

/-- The integrability safeguard for the totalized pairing in
`Contracts.V1.Data.IsSobolevDatum`; see `Contracts/V1/Data.lean:148-155`.
Every genuine `H^s(R^3)` representative has this property by local `L^2`
integrability and rapid decay of Schwartz tests, the same decay used at
`paper/sections/03-torus.tex:617-624`.

**Needs registration.** -/
def HasIntegrableSchwartzPairings (z : SpatialField) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ))

/-- A whole-space `H^s(R^3)` representative of the restriction `z|_Omega`,
bundled with its registered angular Sobolev datum.  The agreement is the
almost-everywhere restriction relation in
`paper/sections/03-torus.tex:601-605`.

**Needs registration / to be aligned with T10's physical-field alias.** -/
structure SobolevExtension (s : ℝ) (Ω : Set Space) (z : SpatialField) where
  field : SpatialField
  agrees_on : field =ᵐ[volume.restrict Ω] z
  pairing_integrable : HasIntegrableSchwartzPairings field
  datum : RealVectorSobolev s
  isDatum : IsSobolevDatum s field datum

/-- `paper/sections/03-torus.tex:601-607`, `eq:restriction-norm`: the quotient
`H^s(Omega)` norm, valid at every real order, including negative orders.  An
empty extension family has infimum `top`, so the quantity is fail-safe.

**Needs registration / to be aligned with T10's physical-field alias.** -/
def restrictionSobolevENorm (s : ℝ) (Ω : Set Space) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ E : SobolevExtension s Ω z, sobolevENorm s E.field

/-- `paper/sections/03-torus.tex:606-607`: the usual `L^2(Omega)` norm, written
as the whole-space `L^2` norm of the zero extension.

**Needs registration.** -/
def domainL2ENorm (Ω : Set Space) (z : SpatialField) : ℝ≥0∞ :=
  eLpNorm (zeroExtension Ω z) 2 volume

/-- Pointwise multiplication of a vector field by the scalar cutoff used at
`paper/sections/03-torus.tex:615-624`.

**Needs registration.** -/
def cutoffProduct (χ : Space → ℝ) (Z : SpatialField) : SpatialField :=
  fun x => χ x • Z x

/-- The class of domains in the bounded-domain layer: open and bounded in the
standard bornology of `R^3`.  Boxes and bounded smooth domains from
`paper/sections/03-torus.tex:633` are intended instances.

**Needs registration.** -/
def IsBoundedOpenDomain (Ω : Set Space) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω

/-- `K compactly contained in Omega` in `paper/sections/03-torus.tex:608`.
Openness of `Omega` is carried by `IsBoundedOpenDomain`.

**Needs registration.** -/
def CompactlyContained (K Ω : Set Space) : Prop := IsCompact K ∧ K ⊆ Ω

/-- `paper/sections/03-torus.tex:608-614`: the paper's "smooth fields supported
in `K`", expressed for the actual zero extension that appears in
`eq:zero-extension`.

**Needs registration / to be aligned with T10's physical-field alias.** -/
def IsSmoothSupportedIn (Ω K : Set Space) (z : SpatialField) : Prop :=
  ContDiff ℝ ∞ (zeroExtension Ω z) ∧ tsupport (zeroExtension Ω z) ⊆ K

/-! ## Target API -/

/-- The bounded-domain norm layer of `paper/sections/03-torus.tex:600-630`.

This is data-carrying because the proof paragraph existentially fixes one
cutoff for each compact inclusion and one multiplier constant for each real
Sobolev order.  The quantifier order makes `C Omega K s` independent of the
field, of every smaller support, and of a shrinking parameter `epsilon`.
-/
structure BoundedDomainNormAPI where
  /-- `paper/sections/03-torus.tex:615-617`: the fixed cutoff associated with
  `K compactly contained in Omega`.  It is deliberately independent of `s`. -/
  χ : (Ω K : Set Space) → Space → ℝ

  /-- `paper/sections/03-torus.tex:612,626-627`: `C_{s,K,Omega}`.  Its arguments
  are exactly the permitted dependencies; in particular there is no field or
  scale argument. -/
  C : (Ω K : Set Space) → ℝ → ℝ

  /-- `paper/sections/03-torus.tex:615-616`: `chi` is smooth. -/
  chi_smooth : ∀ (Ω K : Set Space), IsBoundedOpenDomain Ω → CompactlyContained K Ω →
    ContDiff ℝ ∞ (χ Ω K)

  /-- `paper/sections/03-torus.tex:615-616`: `chi` is compactly supported. -/
  chi_compactSupport : ∀ (Ω K : Set Space), IsBoundedOpenDomain Ω →
    CompactlyContained K Ω →
    HasCompactSupport (χ Ω K)

  /-- `paper/sections/03-torus.tex:615-616`: `chi` has support inside `Omega`. -/
  chi_support : ∀ (Ω K : Set Space), IsBoundedOpenDomain Ω → CompactlyContained K Ω →
    tsupport (χ Ω K) ⊆ Ω

  /-- `paper/sections/03-torus.tex:615-616`: `chi = 1` on an open neighborhood
  of `K`, with the neighborhood itself contained in `Omega`. -/
  chi_one_near : ∀ (Ω K : Set Space), IsBoundedOpenDomain Ω →
    CompactlyContained K Ω →
    ∃ U : Set Space, IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧
      ∀ x : Space, x ∈ U → χ Ω K x = 1

  /-- `paper/sections/03-torus.tex:612,626`: positivity of the multiplier
  constant in `eq:zero-extension`. -/
  C_pos : ∀ (Ω K : Set Space) (s : ℝ), IsBoundedOpenDomain Ω →
    CompactlyContained K Ω →
    0 < C Ω K s

  /-- `paper/sections/03-torus.tex:617-624`: multiplication by the fixed cutoff
  is bounded on `H^s(R^3)` for every real `s`.  It is stated on D01's
  registered datum carrier.  The output datum and its integrable physical
  realization are part of the conclusion, so this clause does not exploit the
  totalized-pairing caveat of `Data.IsSobolevDatum`.

  The constant is explicit and chosen before `Z` and `A`. -/
  cutoff_multiplier : ∀ (Ω K : Set Space) (s : ℝ),
      IsBoundedOpenDomain Ω → CompactlyContained K Ω →
      ∀ (Z : SpatialField) (A : RealVectorSobolev s),
        HasIntegrableSchwartzPairings Z → IsSobolevDatum s Z A →
        ∃ B : RealVectorSobolev s,
          HasIntegrableSchwartzPairings (cutoffProduct (χ Ω K) Z) ∧
          IsSobolevDatum s (cutoffProduct (χ Ω K) Z) B ∧
          ‖B‖ₑ ≤ ENNReal.ofReal (C Ω K s) * ‖A‖ₑ

  /-- `paper/sections/03-torus.tex:616-617`: for every whole-space extension
  `Z` of a field supported in `K`, `chi Z = E_0 z`.  This is the bridge from the
  datum-level multiplier bound to the quotient infimum. -/
  cutoff_extension_identity : ∀ (Ω K : Set Space),
      IsBoundedOpenDomain Ω → CompactlyContained K Ω →
      ∀ (z Z : SpatialField), tsupport (zeroExtension Ω z) ⊆ K →
        Z =ᵐ[volume.restrict Ω] z →
        cutoffProduct (χ Ω K) Z =ᵐ[volume] zeroExtension Ω z

  /-- `paper/sections/03-torus.tex:601-606`, `eq:restriction-norm`, including
  negative `s`: the domain norm is exactly the infimum over whole-space
  extensions.  The right side is displayed rather than hidden behind the local
  definition so a later registered contract pins the quotient convention. -/
  restriction_norm : ∀ (s : ℝ) (Ω : Set Space) (z : SpatialField),
    restrictionSobolevENorm s Ω z =
      ⨅ E : SobolevExtension s Ω z, sobolevENorm s E.field

  /-- `paper/sections/03-torus.tex:606-607`: at order zero the quotient norm is
  the usual domain `L^2` norm.  Strong measurability is the function-level
  representative hypothesis implicit in membership of `L^2(Omega)`. -/
  restriction_zero : ∀ (Ω : Set Space) (z : SpatialField), MeasurableSet Ω →
    AEStronglyMeasurable (zeroExtension Ω z) volume →
    restrictionSobolevENorm 0 Ω z = domainL2ENorm Ω z

  /-- `paper/sections/03-torus.tex:608-614`, `eq:zero-extension`, for every real
  order.  The single conjunction is the displayed chain

  `norm(z, H^s(Omega)) <= norm(E_0 z, H^s(R^3))
      <= C_{s,K,Omega} norm(z, H^s(Omega))`.

  `C Omega K s` is selected outside `z`; hence the same constant works for all
  smaller supports and every sufficiently small member of any concentrating
  `epsilon`-family, exactly as required at
  `paper/sections/03-torus.tex:626-627`. -/
  zero_extension : ∀ (Ω K : Set Space) (s : ℝ),
      IsBoundedOpenDomain Ω → CompactlyContained K Ω →
      ∀ z : SpatialField, IsSmoothSupportedIn Ω K z →
        restrictionSobolevENorm s Ω z ≤ sobolevENorm s (zeroExtension Ω z) ∧
        sobolevENorm s (zeroExtension Ω z) ≤
          ENNReal.ofReal (C Ω K s) * restrictionSobolevENorm s Ω z

end BlowupDensity.Research.T22.DraftA
