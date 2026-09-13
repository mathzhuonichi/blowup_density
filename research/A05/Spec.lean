import Contracts.V1.Data

/-!
# A05 draft specification: critical embeddings for the actual whole-space fields

Task `collaboration/tasks/A05.md`, graph node `A05` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:195-201`.

This file is a **specification draft only**.  It contains `def`s and one
`structure` of obligations.  It proves nothing with mathematical content,
assumes nothing, and introduces no `axiom`, no `sorry` and no abstract `Prop`
placeholder field: every propositional field is a fully spelled-out statement
about explicitly named objects.

## What is specified

Lemma B.1, "Critical embeddings on the two domains" (`lem:critical-embeddings`),
`paper/sections/appendix-b-embeddings.tex:11-49`, **restricted to `R³`** and in
exactly the form the two whole-space regularity propositions consume it:

* Proposition 4.3 (`prop:Rcritical1`), `paper/sections/04-whole-space.tex:82-133`,
  which uses `‖u‖₃ ≤ Cy`, `‖∇u‖₃ + ‖Λu‖₃ ≤ Cz` (`:91-95`) and
  `‖∇u‖₆ ≤ C‖Δu‖₂` (`:112`);
* Proposition 4.4 (`prop:Rcritical2`), `paper/sections/04-whole-space.tex:136-174`,
  which uses `‖u‖₃ ≤ CY`, `‖∇u‖₃ ≤ CZ`, `‖Ju‖₃ ≤ C(Y²+Z²)^{1/2}` (`:152-157`)
  and reuses `‖∇u‖₆ ≤ C‖Δu‖₂` through `eq:RH1`.

The torus half of `eq:critical-embedding-pair`
(`appendix-b-embeddings.tex:19-21`, second inequality) is **out of scope**: no
Section 4 statement uses it, and it has no whole-space realization question.

## Conventions, all inherited from `Contracts.V1.Data`

* Fourier: the manuscript's unitary angular transform
  `ẑ(ξ) = (2π)^{-3/2}∫exp(-i x·ξ)z(x)dx` (`01-introduction.tex:91`), carried by
  `angularFourierDistribution` inside `IsHomogeneousDatum` and by
  `angularRealization` inside `IsSobolevDatum`.  Mathlib's cycles-convention
  `𝓕` never appears in a statement of this file.
* Homogeneous realization: `eq:homogeneous-realization`
  (`02-preliminaries.tex:58-69`) and its positive-order counterpart
  (`appendix-b-embeddings.tex:56-70`) are the single predicate
  `Data.IsHomogeneousDatum`, whose datum norm is `‖v‖_{Ḣ^s}`.
* Vectors and tensors: "For vectors and tensors we sum the squared component
  norms" (`01-introduction.tex:103`).  On the `L^p` side that is the Euclidean
  pointwise norm of `Space = EuclideanSpace ℝ (Fin 3)` and the `PiLp 2` norm of
  `Data.spatialGradient`; on the Sobolev side it is `RealVectorSobolev`.
* Fields: `MemHInfty` (`02-preliminaries.tex:12` eq:Rinitial) is the
  "smooth `H^∞` fields" class of `appendix-b-embeddings.tex:47-49`.
  Solenoidality is irrelevant to every clause here and is not assumed.
* Every norm is `ℝ≥0∞`-valued and no norm is routed through `.toReal`, so the
  paper's "whenever the indicated homogeneous norms are finite"
  (`appendix-b-embeddings.tex:27`) is the fail-safe `⊤` on the right-hand side
  rather than a side condition.

## Why `Λ` appears as a relation and not as an operator

`research/D01/RECONCILIATION.md:192-197` leaves `Λ = (-Δ)^{1/2}` to A05.  Two of
the consumed clauses (`‖Λu‖₃`, `‖Ju‖₃`) are `L³` norms **of the transformed
field**, so a quantity built from `u` alone cannot express them; and
`appendix-b-embeddings.tex:101` refuses `Ḣ^{3/2}` as a space, so `Λ^{3/2}u`
cannot be produced by a total operator on a completed space either.
`IsRieszPower` / `IsBesselPower` below are therefore graph relations on physical
fields, defined *only* through `Data.IsHomogeneousDatum` and
`Data.IsSobolevDatum`.  They are single-valued and norm-preserving by the
`rieszPowerNorm` / `besselPowerNorm` clauses, which is all the propositions use.
No `𝓢' → 𝓢'` multiplier by `|ξ|` is introduced: `Paper3/HomogeneousRealization.lean:7`
records that `‖ξ‖` is not `HasTemperateGrowth`, so no such multiplier exists in
tree.
-/

noncomputable section

namespace BlowupDensity.A05.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.RealSobolev (FourierData)
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. The physical fields Lemma B.1 is applied to -/

/-- The time-independent lift of a spatial field, so that the pinned upstream
spacetime operators `spatialDerivative`, `spatialLaplacian` and
`Data.spatialGradient` can be reused verbatim on a fixed-time slice.  This is
the same device `Data.IsSolenoidal` uses (`Contracts/V1/Data.lean:497`). -/
def lift (v : SpatialField) : SpaceTimeField := fun z => v z.2

/-- `appendix-b-embeddings.tex:96` "Apply the `a = 1/2` inequality to each
`∂_jv`": the `j`-th partial derivative of a spatial field, as a spatial field.
It is the `j`-th entry of `gradientTensor`. -/
def partialDeriv (j : Fin 3) (v : SpatialField) : SpatialField :=
  fun x => spatialDerivative (lift v) 0 x (coordinateVector j)

/-- `04-whole-space.tex:91,112`, the tensor `∇u`.  This is `Data.spatialGradient`
(`Contracts/V1/Data.lean:446`) on the time-independent lift, so its pointwise
norm is the Frobenius quantity `(∑_{i,j}|∂_iv_j|²)^{1/2}` of
`01-introduction.tex:103` and **not** an operator norm. -/
def gradientTensor (v : SpatialField) : Space → WithLp 2 (Fin 3 → Space) :=
  fun x => spatialGradient (lift v) 0 x

/-- `04-whole-space.tex:110-112`, the field `Δu` appearing in the continuation
estimate.  This is the pinned upstream componentwise Euclidean Laplacian
`∑ᵢ∂ᵢ∂ᵢu` (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:76`)
on the time-independent lift. -/
def laplacian (v : SpatialField) : SpatialField :=
  fun x => spatialLaplacian (lift v) 0 x

/-! ## 2. The homogeneous quantity of a physical field -/

/-- `appendix-b-embeddings.tex:27` `‖v‖_{Ḣ^s}` **for a physical field**, the
homogeneous counterpart of `Data.sobolevENorm` (`Contracts/V1/Data.lean:189`):
the `L²` norm of the order-`s` homogeneous datum of the tempered vector
distribution that the field represents, and `⊤` when the field has no such
datum.  The empty infimum in `ℝ≥0∞` is `⊤`, so this is total and fail-safe.

`Data.lean` defines the datum predicate `IsHomogeneousSliceDatum`
(`Contracts/V1/Data.lean:364`) and the distribution-level norm
`homogeneousVectorENorm` (`:349`) but not this physical-field quantity, because
prop:Renergy needs only the time-integrated version.  Lemma B.1 needs it
slicewise.

This is deliberately **not** `Data.homogeneousFourierENorm` (`:407`): that one
is a literal pointwise Bochner Fourier integral and its own docstring forbids
its use on a general `H^∞` slice, where it silently totalizes to a junk `0`.
Every field below is an `H^∞` field that need not be `L¹`, so only the datum
form is honest here. -/
def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

/-- `04-whole-space.tex:150` `Z = ‖∇u‖_{H^{1/2}}`: the **inhomogeneous** Sobolev
quantity of the gradient tensor, assembled from the nine component norms by
`01-introduction.tex:103` "sum the squared component norms".  `Data.sobolevENorm`
already sums the three components of each `∂_jv`. -/
def tensorSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  (∑ j : Fin 3, sobolevENorm s (partialDeriv j z) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `appendix-b-embeddings.tex:14` `p_a = 6/(3-2a)`, the critical exponent of
`eq:critical-embedding-pair`.  Numerically identical to the in-tree
`NSFormalization.RieszPotentialLp.targetExponent`
(`Source/RieszPotentialLp.lean:14`), which a binding should identify. -/
def criticalExponent (a : ℝ) : ℝ := 6 / (3 - 2 * a)

/-! ## 3. `Λ^a` and `J^a` as single-valued relations on physical fields -/

/-- `appendix-b-embeddings.tex:8-9` `Λ = (-Δ)^{1/2}` has symbol `|ξ|` on `R³`;
here the order-`a` power, as the relation `w = Λ^a v` between two physical real
vector fields.

The relation says exactly that the two fields have tempered vector distributions
`V`, `W` sharing one frequency datum `G`: `V̂ᵢ = |ξ|^{-a}G` and `Ŵᵢ = G`, i.e.
`Ŵ = |ξ|^a V̂`, both read in the manuscript's angular normalization through
`Data.IsHomogeneousDatum` (`Contracts/V1/Data.lean:321`) at orders `a` and `0`.
Consequently `‖w‖₂ = ‖G‖₂ = ‖v‖_{Ḣ^a}`, which is `04-whole-space.tex:91`'s
`y = ‖Λ^{1/2}u‖₂` and `z = ‖Λ^{3/2}u‖₂`; that consequence is the
`rieszPowerNorm` clause, not part of this definition.

`AEStronglyMeasurable w` is part of the relation, not a downstream hypothesis:
without it `eLpNorm w p volume` degenerates to a lower Lebesgue integral and the
`L³` bounds on `Λu` could be met by a nonmeasurable representative.  It is free
in every application, since `w` is an `L²` field. -/
def IsRieszPower (a : ℝ) (v w : SpatialField) : Prop :=
  AEStronglyMeasurable w volume ∧
    ∃ V W : VectorDistribution,
      IsSliceDistribution v V ∧ IsSliceDistribution w W ∧
        ∀ i : Fin 3, ∃ G : FourierData,
          IsHomogeneousDatum a G (V i) ∧ IsHomogeneousDatum 0 G (W i)

/-- `02-preliminaries.tex:51` and `04-whole-space.tex:147` `J = (I-Δ)^{1/2}`,
symbol `(1+|ξ|²)^{1/2}`; here the order-`a` power, as the relation `w = J^a v`.

Same shape as `IsRieszPower`, with the inhomogeneous weight: the two fields
share one datum through `Data.IsSobolevDatum` (`Contracts/V1/Data.lean:160`) at
orders `a` and `0`, i.e. `Ŵ = ⟨ξ⟩^a V̂`.  The two datum carriers have distinct
Lean types, so the sharing is stated on their common `FourierData` components,
exactly as `Data.IsHomogeneousVectorDatum` (`:355`) coerces them.

Only `a = 1` is used (`04-whole-space.tex:152`, `‖Ju‖₃`). -/
def IsBesselPower (a : ℝ) (v w : SpatialField) : Prop :=
  AEStronglyMeasurable w volume ∧
    ∃ (A : RealVectorSobolev a) (B : RealVectorSobolev 0),
      IsSobolevDatum a v A ∧ IsSobolevDatum 0 w B ∧
        ∀ i : Fin 3, ((A i : FourierData)) = ((B i : FourierData))

/-! ## 4. The contract -/

/-- Lemma B.1 (`lem:critical-embeddings`, `appendix-b-embeddings.tex:11-49`) on
`R³`, in the form Propositions 4.3 and 4.4 consume it.

All constants are structure fields, hence quantified **outside** every field,
every viscosity and every solution: `appendix-b-embeddings.tex:108-110`, "All
constants depend only on the fixed exponents, domain, and norm conventions, not
on the field or its frequency support." -/
structure CriticalEmbeddingAPI where
  /-- `appendix-b-embeddings.tex:19` `C_a` of eq:critical-embedding-pair, the
  Euclidean constant at order `a`.  Only `a ∈ {1/2, 1}` is constrained below;
  the paper allows dependence on `a` and on the number of components. -/
  C : ℝ → ℝ
  /-- `appendix-b-embeddings.tex:17` "there are finite constants". -/
  C_pos : ∀ a : ℝ, 0 < C a
  /-- `appendix-b-embeddings.tex:31` eq:critical-derived, second line: the one
  constant bounding `‖∇v‖₃ + ‖Λv‖₃`. -/
  Cderiv : ℝ
  /-- Positivity of `Cderiv`. -/
  Cderiv_pos : 0 < Cderiv
  /-- `appendix-b-embeddings.tex:32` eq:critical-derived, third line, and
  `04-whole-space.tex:112`: the constant of `‖∇v‖₆ ≤ C‖Δv‖₂`. -/
  Csix : ℝ
  /-- Positivity of `Csix`. -/
  Csix_pos : 0 < Csix
  /-- `04-whole-space.tex:152-155`: the constant of `‖Jv‖₃ ≤ C‖v‖_{H^{3/2}}`,
  the inhomogeneous multiplier form Proposition 4.4 tests against. -/
  Cbessel : ℝ
  /-- Positivity of `Cbessel`. -/
  Cbessel_pos : 0 < Cbessel

  /-- `appendix-b-embeddings.tex:97-99` "The Euclidean statements use the
  preceding realizations of the derivatives", and the task's "same real
  vector/tensor distribution" clause: a physical field has **one** tempered
  vector distribution, so the `a = 1/2` completion and the `a = 1` completion of
  the same field — in particular of the same `∂_jv` — are completions of the
  same object and their `L^{p_a}` representatives are representatives of it.
  Stated at two independent orders `a`, `b`, which is how the lemma's proof uses
  it (`a = 1/2` for `L³`, `a = 1` for `L⁶`, on one `∂_jv`). -/
  sameRealDistribution :
    ∀ (a b : ℝ) (z : SpatialField) (U V : VectorDistribution)
      (Ga : RealVectorSobolev a) (Gb : RealVectorSobolev b),
      IsSliceDistribution z U → IsHomogeneousVectorDatum a U Ga →
      IsSliceDistribution z V → IsHomogeneousVectorDatum b V Gb →
      U = V

  /-- `appendix-b-embeddings.tex:65-70` "Thus this construction gives a unique
  `L^{p_a}` representative for every element of the completion", and
  `02-preliminaries.tex:63-70` "an isometric bijection onto `L²` … no polynomial
  ambiguity": the homogeneous datum of a physical field is unique, so
  `dotHomogeneousENorm` is attained rather than a strict infimum.  Restricted to
  the manuscript's range `-3/2 < s < 3/2` (`02-preliminaries.tex:70`,
  `appendix-b-embeddings.tex:44`). -/
  homogeneousDatumUnique :
    ∀ s : ℝ, -(3 / 2) < s → s < 3 / 2 →
      ∀ (z : SpatialField) (G K : RealVectorSobolev s),
        IsHomogeneousSliceDatum s z G → IsHomogeneousSliceDatum s z K → G = K

  /-- `01-introduction.tex:105` with `|ξ|^{2a} ≤ (1+|ξ|²)^a` for `a ≥ 0`:
  `‖z‖_{Ḣ^a} ≤ ‖z‖_{H^a}`.  Because the left side is `⊤` off the homogeneous
  space, this simultaneously asserts that an `H^a` field **has** an order-`a`
  homogeneous datum, which is `appendix-b-embeddings.tex:69-70` "It includes all
  Schwartz functions and all `H^∞` fields with finite displayed homogeneous
  norm".  `research/section4/STATEMENTS.md:602` requires exactly this at
  `a ∈ {1/2, 1}` for Proposition 4.4; the range `0 ≤ a < 3/2` is the
  manuscript's. -/
  homogeneousLeSobolev :
    ∀ a : ℝ, 0 ≤ a → a < 3 / 2 →
      ∀ z : SpatialField, MemHInfty z →
        dotHomogeneousENorm a z ≤ sobolevENorm a z

  /-- `appendix-b-embeddings.tex:103` "Plancherel and `∑_j|ξ_j|² = |ξ|²`",
  combined with the previous clause at `a = 1/2`:
  `‖v‖_{Ḣ^{3/2}} ≤ ‖∇v‖_{H^{1/2}} = Z`.  This is the step by which Proposition
  4.4 reads Lemma B.1's `Ḣ^{3/2}` right-hand side against its inhomogeneous
  `Z` (`04-whole-space.tex:150-157`, `research/section4/STATEMENTS.md:600-603`).
  It is an inequality and not the exact identity `‖u‖²_{H^{3/2}} = Y² + Z²`,
  which is D01's weight identity and is owned by R44. -/
  dotThreeHalvesLeGradientSobolev :
    ∀ v : SpatialField, MemHInfty v →
      dotHomogeneousENorm (3 / 2) v ≤ tensorSobolevENorm (1 / 2) v

  /-- `appendix-b-embeddings.tex:65-70`: the completion's unique `L^{p_a}`
  representative, `p_a = 6/(3-2a)`, exists for every `H^∞` field with finite
  homogeneous norm.  Without this clause the estimates below would be bounds on
  a possibly infinite left-hand side. -/
  criticalRepresentative :
    ∀ a : ℝ, 0 < a → a < 3 / 2 →
      ∀ v : SpatialField, MemHInfty v → dotHomogeneousENorm a v ≠ ⊤ →
        MemLp v (ENNReal.ofReal (criticalExponent a)) volume

  /-- `04-whole-space.tex:91` "Set `Λ = (-Δ)^{1/2}`, `y = ‖Λ^{1/2}u‖₂`,
  `z = ‖Λ^{3/2}u‖₂`": the field `Λ^a v` exists, as an `L²` field, exactly when
  the homogeneous norm of `v` is finite.  Together with `rieszPowerNorm` this is
  the whole content of `Λ` that Section 4 uses.  The range `0 < a < 3/2` is
  `appendix-b-embeddings.tex:44`; `a = 3/2` is admitted as well because
  `‖Λ^{3/2}u‖₂` is a quantity the manuscript writes on `H^∞` fields even though
  `appendix-b-embeddings.tex:101` builds no `Ḣ^{3/2}` space. -/
  rieszPowerExists :
    ∀ a : ℝ, 0 < a → a ≤ 3 / 2 →
      ∀ v : SpatialField, MemHInfty v → dotHomogeneousENorm a v ≠ ⊤ →
        ∃ w : SpatialField, IsRieszPower a v w ∧ MemLp w 2 volume

  /-- `04-whole-space.tex:91` and `appendix-b-embeddings.tex:31`:
  `‖Λ^a v‖₂ = ‖v‖_{Ḣ^a}`.  This is the identification that makes `y` and `z` of
  Proposition 4.3 the same numbers as Lemma B.1's right-hand sides, and it makes
  `Λ^a v` single-valued up to a null set. -/
  rieszPowerNorm :
    ∀ a : ℝ, 0 < a → a ≤ 3 / 2 →
      ∀ v w : SpatialField, MemHInfty v → IsRieszPower a v w →
        eLpNorm w 2 volume = dotHomogeneousENorm a v

  /-- `04-whole-space.tex:147-152`: the field `J^a v` exists, as an `L²` field,
  exactly when the inhomogeneous norm of `v` is finite.  For `MemHInfty v` and
  integer `a` the hypothesis is automatic; it is kept so the clause is usable at
  `a = 1/2` as well. -/
  besselPowerExists :
    ∀ a : ℝ, 0 ≤ a →
      ∀ v : SpatialField, MemHInfty v → sobolevENorm a v ≠ ⊤ →
        ∃ w : SpatialField, IsBesselPower a v w ∧ MemLp w 2 volume

  /-- `04-whole-space.tex:147-152`: `‖J^a v‖₂ = ‖v‖_{H^a}`, the inhomogeneous
  counterpart of `rieszPowerNorm`, which is how Proposition 4.4's `Y`, `Z` and
  `‖u‖_{H^{3/2}}` refer to one field. -/
  besselPowerNorm :
    ∀ a : ℝ, 0 ≤ a →
      ∀ v w : SpatialField, MemHInfty v → IsBesselPower a v w →
        eLpNorm w 2 volume = sobolevENorm a v

  /-- `appendix-b-embeddings.tex:22-25` "Componentwise application gives the same
  statements for vector and tensor fields": the `L^p` membership of the gradient
  **tensor** follows from the `L^p` membership of its three vector columns, with
  no constant, because `Data.spatialGradient` is the `PiLp 2` assembly.  This is
  the structural half of the componentwise clause; the constant-bearing half is
  absorbed into `Cderiv` and `Csix`. -/
  tensorMemLp :
    ∀ (p : ℝ≥0∞) (v : SpatialField), MemHInfty v →
      (∀ j : Fin 3, MemLp (partialDeriv j v) p volume) →
        MemLp (gradientTensor v) p volume

  /-- `appendix-b-embeddings.tex:19` eq:critical-embedding-pair, Euclidean half,
  at the two orders the article uses: `‖v‖_{L^{p_a}} ≤ C_a‖Λ^a v‖₂` with the
  right-hand side written as `‖v‖_{Ḣ^a}`.  `a = 1/2` gives `p_a = 3` and `a = 1`
  gives `p_a = 6`; `04-whole-space.tex:112` invokes the second by name ("the
  `Ḣ^1 → L^6` case of Lemma B.1").  Vacuous when `v ∉ Ḣ^a`, which is the paper's
  "whenever the indicated homogeneous norms are finite". -/
  embeddingPair :
    ∀ a : ℝ, a = 1 / 2 ∨ a = 1 →
      ∀ v : SpatialField, MemHInfty v →
        eLpNorm v (ENNReal.ofReal (criticalExponent a)) volume ≤
          ENNReal.ofReal (C a) * dotHomogeneousENorm a v

  /-- `appendix-b-embeddings.tex:29` eq:critical-derived, first line, as
  `04-whole-space.tex:93` (`‖u‖₃ ≤ Cy`) and `:171` (`‖u‖₃ ≤ CY`) consume it:
  `‖v‖₃ ≤ C‖v‖_{Ḣ^{1/2}}` for the velocity slice itself.  It is the `a = 1/2`
  instance of `embeddingPair` with the exponent evaluated, kept as a separate
  field so that R43/R44 need no numeric rewriting of `ENNReal.ofReal (6/(3-1))`. -/
  velocityCriticalL3 :
    ∀ v : SpatialField, MemHInfty v →
      eLpNorm v 3 volume ≤ ENNReal.ofReal (C (1 / 2)) * dotHomogeneousENorm (1 / 2) v

  /-- `appendix-b-embeddings.tex:30-31` eq:critical-derived, second line, as
  `04-whole-space.tex:94` consumes it: `‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖_{Ḣ^{3/2}}`, one
  constant for the sum, with `w = Λv` supplied by the relation.  The gradient is
  the tensor `gradientTensor v`, i.e. the componentwise application of
  `appendix-b-embeddings.tex:22-25`, and the right-hand side is
  `Proposition 4.3`'s `z` by `rieszPowerNorm` at `a = 3/2`.

  On the right-hand side `s = 3/2` sits at the endpoint that
  `appendix-b-embeddings.tex:101` refuses to complete into a space.  The
  quantity is nevertheless well posed here: `Data.IsHomogeneousDatum (3/2) G U`
  demands `Integrable (φ · |ξ|^{-3/2}G)`, and for an `H^∞` field
  `|ξ|^{-3/2}G = v̂ ∈ L²`, so the clause holds.  No `Ḣ^{3/2}` space, and no
  `Ḣ^{3/2} ↪ L^∞`, is asserted anywhere in this contract
  (`appendix-b-embeddings.tex:101-102`). -/
  derivativeCriticalL3 :
    ∀ v w : SpatialField, MemHInfty v → IsRieszPower 1 v w →
      eLpNorm (gradientTensor v) 3 volume + eLpNorm w 3 volume ≤
        ENNReal.ofReal Cderiv * dotHomogeneousENorm (3 / 2) v

  /-- `appendix-b-embeddings.tex:32` eq:critical-derived, third line, as
  `04-whole-space.tex:110-112` consumes it: `‖∇v‖₆ ≤ C‖Δv‖₂`.  The manuscript
  derives it from the `a = 1` case applied to each `∂_jv` together with the
  Plancherel identity `‖D²v‖₂ = ‖Δv‖₂`; the identity is folded into this field so
  that the right-hand side is literally the `‖Δu‖₂` of `eq:RH1` and no separate
  `D²` object is needed.  Reused verbatim by Proposition 4.4
  (`04-whole-space.tex:171`). -/
  gradientLSix :
    ∀ v : SpatialField, MemHInfty v →
      eLpNorm (gradientTensor v) 6 volume ≤
        ENNReal.ofReal Csix * eLpNorm (laplacian v) 2 volume

  /-- `04-whole-space.tex:152-155`: `‖Jv‖₃ ≤ C(Y²+Z²)^{1/2} = C‖v‖_{H^{3/2}}`,
  the third factor of Proposition 4.4's trilinear bound.  This is the `a = 1/2`
  embedding applied to `Jv`, whose homogeneous `Ḣ^{1/2}` norm is dominated by
  `‖v‖_{H^{3/2}}`; both steps are collapsed into the single constant `Cbessel`
  because that is the only form Proposition 4.4 uses. -/
  besselCriticalL3 :
    ∀ v w : SpatialField, MemHInfty v → IsBesselPower 1 v w →
      eLpNorm w 3 volume ≤ ENNReal.ofReal Cbessel * sobolevENorm (3 / 2) v

end BlowupDensity.A05.Draft
