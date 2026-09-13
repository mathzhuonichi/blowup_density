import Contracts.V1.Data

/-!
# A03 draft specification: whole-space tame products and bounded representatives

Task `collaboration/tasks/A03.md`, graph node `A03` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:214-223`.

This file is a **specification draft only**.  It contains `def`s and one
`structure` of obligations.  It proves nothing with mathematical content,
assumes nothing, and introduces no `axiom`, no `sorry` and no abstract `Prop`
placeholder field: every propositional field is a fully spelled-out statement
about explicitly named objects.

## What is specified

Lemma A.1, "Sobolev multiplication and embeddings" (`lem:calculus`),
`paper/sections/appendix-a-local-theory.tex:7-27`, **restricted to `R³`** and
in exactly the form Section 4 and Appendix A consume it:

* `eq:Rproduct` (`:9-13`), both clauses —
  `‖vw‖_{H^m} ≤ C_m(‖v‖_{H²}‖w‖_{H^m} + ‖w‖_{H²}‖v‖_{H^m})` for integers
  `m ≥ 2`, and `‖v‖_∞ ≤ C‖v‖_{H²}`;
* `eq:algebra` (`:16`) and `eq:tame` (`:17-18`) for integers `k ≥ 3`;
* the componentwise vector/tensor form and the product **difference** bound
  that `:50-52` records ("The argument applies componentwise to vectors and
  tensors, and factorization gives the corresponding product difference
  bound").

The consumers, and the exact clause each one needs:

* **Theorem 4.2** (`thm:Rinsert`, `paper/sections/04-whole-space.tex:31-46`),
  lifespan `≤ T` step at `:53`: "An extension through `T` would be bounded in
  `C_tH²` on a neighborhood of `T`, hence bounded in `L^∞_x` by
  `eq:Rproduct`".  This is `supNorm_le_of_continuous` below, applied to the
  smooth velocity slice at each time.  `research/section4/STATEMENTS.md:261-262`,
  `:314`, `:1120-1122` and `:1321` record that this is the edge `A03 → R42`
  that `DEPENDENCY_GRAPH.md` is missing.
* **A04** (`collaboration/tasks/A04.md`) through `eq:Rhigh`
  (`appendix-a-local-theory.tex:132-137`): the nonlinear term of the order-`m`
  energy identity is bounded by `eq:Rproduct` applied to `u ⊗ u`, i.e. by
  `outerProductTame` below, followed by Cauchy–Schwarz against `‖∇u‖_{H^m}`.
  The Cauchy–Schwarz step, the integration by parts and the Grönwall are
  A04's, not this contract's.
* **A01/A02** (`prop:local`) through the uniqueness coefficient
  `‖∇u₂‖_∞` at `appendix-a-local-theory.tex:120-123`, "bounded on compact
  common intervals, since `u₂ ∈ C_tH³`".  This is `gradientSupNorm_le`
  composed with `gradientSobolevENorm_le`.
* **A01** additionally lists this contract as its unit **A1**
  (`research/A01/COMPARISON.md:197`, `:326-332`): the tame product
  `‖u⊗u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` and `‖v‖_∞ ≤ C‖v‖_{H²}` **on the D01
  carrier**, which is what the clauses below are stated on.

## What is deliberately out of scope

* The torus.  `lem:calculus` is stated "for either domain"
  (`appendix-a-local-theory.tex:8`); Section 3 is deferred and no whole-space
  statement of Section 4 uses the periodic half.
* `H¹ ↪ L⁶` (`:20`) and `eq:embeddings` (`:22-26`).  Those are the shared
  lemma's *embedding* clauses, proved by `lem:critical-embeddings` (`:54-55`)
  and owned by **A05**; `research/A05/Spec.lean` states them.  The task card
  says so explicitly: "The embedding clauses of shared Lemma A.1 are supplied
  by A05."  The one embedding kept here is the `L^∞` clause of `eq:Rproduct`,
  which A05's contract does not carry and Theorem 4.2 needs.
* `∇·(u⊗u) = (u·∇)u` for divergence-free smooth `u`.  That is A01's unit
  **E1** (`research/A01/COMPARISON.md:190`), pure calculus on the upstream
  `advection`; both bilinear forms are given norms here so that either side of
  that identity can be estimated, but the identity itself is not asserted.
* Monotonicity `‖z‖_{H^s} ≤ ‖z‖_{H^r}` for `s ≤ r`, and uniqueness of the
  order-`s` datum.  `research/section4/STATEMENTS.md:1112-1116` assigns the
  first to D01 §8.2 and `Contracts/V1/Data.lean:145-146` books the second as
  D01 unit L1.  Neither is restated.

## Conventions, all inherited from `Contracts.V1.Data`

* Fourier: the manuscript's unitary angular transform
  `ẑ(ξ) = (2π)^{-3/2}∫exp(-i x·ξ)z(x)dx` (`01-introduction.tex:91`), carried by
  `angularRealization` inside `Data.IsSobolevDatum` and inside
  `IsScalarSobolevDatum` below.  Mathlib's cycles-convention `𝓕` never appears
  in a statement of this file.
* Vectors and tensors: "For vectors and tensors we sum the squared component
  norms" (`01-introduction.tex:103`).  On the Sobolev side that is
  `Data.RealVectorSobolev` for a three-vector and the `PiLp 2` assembly
  `columnsSobolevENorm` below for a `3×3` tensor; on the pointwise side it is
  the Euclidean norm of `Space` and the `PiLp 2` norm of
  `Data.spatialGradient`.
* Fields: every clause is stated about a **physical** field
  `Data.SpatialField = Space → Space`, or about a physical scalar
  `Space → ℝ`, never about an abstract datum.  The product is therefore the
  literal pointwise product, and no separate "the completed product is
  multiplication" identification clause is needed — that identification is
  built into the shape of the statement.  This is the task's "actual physical
  multiplication for the energy argument".
* Every norm is `ℝ≥0∞`-valued and no norm is routed through `.toReal`, so a
  field outside the space makes a right-hand side `⊤` rather than making a
  bound vacuous.  Conversely a bound with a finite right-hand side *asserts*
  that the left-hand side has a datum, which is the "closed under
  multiplication" half of `eq:Rproduct`.
* Constants are structure fields, hence quantified **outside** every field,
  every viscosity and every solution.  `eq:Rproduct` writes them `C_m` and
  `C`: they depend only on the integer order, never on the field, its support
  or its frequency support.  This is the task's "with constants independent of
  support".

## Why the admissibility predicates are there

`Data.sobolevENorm` is an infimum over data, and `Contracts/V1/Data.lean:148-155`
records that it totalizes to a junk `0` on a slice that pairs integrably with
no Schwartz test at all.  On such a slice `‖z‖_∞ ≤ C‖z‖_{H²}` would be a false
statement, not a vacuous one.  `MemHmVector` and `MemHmScalar` below add the
one hypothesis that rules this out — genuine `L²` membership of the physical
field — and `memHInfty_memHm` says that every field Section 4 actually applies
the lemma to, namely a smooth `H^∞` field, satisfies it.
-/

noncomputable section

namespace BlowupDensity.A03.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData RealSobolevHilbert)
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. The physical fields Lemma A.1 is applied to

`04-whole-space.tex:53` applies the lemma to a velocity slice; `eq:Rhigh`
(`appendix-a-local-theory.tex:132-137`) applies it to `u ⊗ u`;
`appendix-a-local-theory.tex:120` applies it to `∇u₂`.  All three are built
from a spatial field by the pinned upstream spacetime operators, evaluated on
the time-independent lift. -/

/-- The time-independent lift of a spatial field, so that the pinned upstream
`spatialDerivative`, `advection` and `Data.spatialGradient` can be reused
verbatim on a fixed-time slice.  This is the device `Data.IsSolenoidal` uses
(`Contracts/V1/Data.lean:504`), and it is the same `lift` as
`research/A05/Spec.lean`. -/
def lift (v : SpatialField) : SpaceTimeField := fun z => v z.2

/-- `appendix-a-local-theory.tex:50` "The argument applies componentwise":
the `j`-th partial derivative of a spatial field, again as a spatial field. -/
def partialDeriv (j : Fin 3) (v : SpatialField) : SpatialField :=
  fun x => spatialDerivative (lift v) 0 x (coordinateVector j)

/-- `appendix-a-local-theory.tex:120`, the tensor `∇u₂` whose `L^∞` norm is the
uniqueness coefficient.  This is `Data.spatialGradient`
(`Contracts/V1/Data.lean:453`) on the time-independent lift, so its pointwise
norm is the Frobenius quantity `(∑_{i,j}|∂_iv_j|²)^{1/2}` of
`01-introduction.tex:103` and **not** an operator norm.  Identical to
`research/A05/Spec.lean`'s `gradientTensor`. -/
def gradientTensor (v : SpatialField) : Space → WithLp 2 (Fin 3 → Space) :=
  fun x => spatialGradient (lift v) 0 x

/-- `01-introduction.tex:83` eq:NS and `02-preliminaries.tex:81` eq:projected:
the bilinear advection `(u·∇)v`, as a spatial field.  On the diagonal it is the
pinned upstream nonlinearity: `advectionOf u u = fun x => advection (lift u) 0 x`
holds by `rfl`, because
`advection w t x = spatialDerivative w t x (w (t,x))`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:63`) and
`lift u (0,x) = u x`. -/
def advectionOf (u v : SpatialField) : SpatialField :=
  fun x => spatialDerivative (lift v) 0 x (u x)

/-- `appendix-a-local-theory.tex:17` eq:tame and `:112` eq:mild: the `j`-th
column of the tensor `u ⊗ v`, i.e. the vector field `x ↦ u_j(x)·v(x)`.  The
nine entries of `u ⊗ v` are the three Euclidean components of the three
columns, which is how `01-introduction.tex:103` "sum the squared component
norms" is realized below. -/
def outerColumn (u v : SpatialField) (j : Fin 3) : SpatialField :=
  fun x => (u x j) • v x

/-- Pointwise difference of two spatial fields, `u - v`, spelled out so that no
`Pi` instance has to be inferred inside a statement. -/
def diffField (u v : SpatialField) : SpatialField := fun x => u x - v x

/-! ## 2. Scalar and tensor Sobolev quantities

`Contracts/V1/Data.lean` supplies `sobolevENorm` for a real **three-vector**
field only.  `eq:Rproduct`'s `‖vw‖_{H^m}` is a product of scalars, and
`eq:tame`'s `‖u⊗u‖_{H^k}` is a `3×3` tensor, so both a scalar and a tensor
quantity are needed.  Both are built from the same
`angularRealization`-pairing that `Data.IsSobolevDatum` uses, so that "`H^m`"
means one thing throughout. -/

/-- `01-introduction.tex:91,94` and `02-preliminaries.tex:72`, the scalar case
of `Data.IsSobolevDatum` (`Contracts/V1/Data.lean:160`): `A` is *the* order-`s`
angular real Sobolev datum of the physical scalar `a`, in the sense that the
distribution it realizes pairs with every Schwartz test exactly as `a` does.
`RealSobolevHilbert s` is precisely the component type of
`Data.RealVectorSobolev s`
(`formalization/NSFormalization/Paper3/RealVectorPositiveDensity.lean:15`), so
this is literally one component of the vector predicate.

The same totalization caveat as `Data.IsSobolevDatum` applies, and is handled
the same way, by `MemHmScalar`. -/
def IsScalarSobolevDatum (s : ℝ) (a : Space → ℝ) (A : RealSobolevHilbert s) : Prop :=
  ∀ ψ : SchwartzMap Space ℂ,
    angularRealization s (A : FourierData) ψ = ∫ x : Space, ψ x * ((a x : ℝ) : ℂ)

/-- `01-introduction.tex:94`, `‖a‖_{H^s(R³)}` for a physical **scalar** field:
the norm of the order-`s` datum, and `⊤` when `a` has none.  The empty infimum
in `ℝ≥0∞` is `⊤`, so this is total.  Exactly `Data.sobolevENorm`
(`Contracts/V1/Data.lean:189`) with `Fin 3` replaced by a point. -/
def scalarSobolevENorm (s : ℝ) (a : Space → ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : RealSobolevHilbert s // IsScalarSobolevDatum s a A}, ‖A.1‖ₑ

/-- `01-introduction.tex:103` "For vectors and tensors we sum the squared
component norms": the order-`s` Sobolev norm of a `3×3` tensor field presented
by its three columns.  `Data.sobolevENorm` already sums the three Euclidean
components of each column, so this is the full nine-entry quantity. -/
def columnsSobolevENorm (s : ℝ) (T : Fin 3 → SpatialField) : ℝ≥0∞ :=
  (∑ j : Fin 3, sobolevENorm s (T j) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `appendix-a-local-theory.tex:134` `‖∇u‖_{H^m}`: the tensor norm of the
gradient.  Numerically the same quantity as `research/A05/Spec.lean`'s
`tensorSobolevENorm`, which is stated there for `Z = ‖∇u‖_{H^{1/2}}` of
Proposition 4.4; the two contracts must agree on it and do, both being
`(∑_j ‖∂_j v‖²_{H^s})^{1/2}`. -/
def gradientSobolevENorm (s : ℝ) (v : SpatialField) : ℝ≥0∞ :=
  columnsSobolevENorm s (fun j => partialDeriv j v)

/-- `appendix-a-local-theory.tex:17` eq:tame, `‖u ⊗ v‖_{H^s}`. -/
def outerSobolevENorm (s : ℝ) (u v : SpatialField) : ℝ≥0∞ :=
  columnsSobolevENorm s (outerColumn u v)

/-- `appendix-a-local-theory.tex:51-52` "factorization gives the corresponding
product difference bound", and its use in the whole-space local theory,
`paper/originals/local/paper_3_whole_space.tex:157,192`:
`‖u⊗u − v⊗v‖_{H^s}`. -/
def outerDiffSobolevENorm (s : ℝ) (u v : SpatialField) : ℝ≥0∞ :=
  columnsSobolevENorm s
    (fun j => diffField (outerColumn u u j) (outerColumn v v j))

/-! ## 3. The admissible classes -/

/-- The class Lemma A.1 is applied to on `R³` at integer order `m`: a physical
real three-vector field that is genuinely square integrable and carries an
order-`m` datum.  `MemLp` is what rules out the junk totalization recorded at
`Contracts/V1/Data.lean:148-155`; the finiteness clause is membership in `H^m`.
`02-preliminaries.tex:29-30` — "a classical velocity belongs to `C([0,S];H^m)`
for every integer `m ≥ 0`" — is the manuscript's version of this class. -/
def MemHmVector (m : ℕ) (z : SpatialField) : Prop :=
  MemLp z 2 volume ∧ sobolevENorm (m : ℝ) z ≠ ⊤

/-- The scalar counterpart of `MemHmVector`, for the factors of
`eq:Rproduct`'s `vw`. -/
def MemHmScalar (m : ℕ) (a : Space → ℝ) : Prop :=
  MemLp a 2 volume ∧ scalarSobolevENorm (m : ℝ) a ≠ ⊤

/-! ## 4. The contract -/

/-- Lemma A.1 (`lem:calculus`, `paper/sections/appendix-a-local-theory.tex:7-27`)
on `R³`, in the form Theorem 4.2, A04 and `prop:local` consume it.

All constants are structure fields, hence quantified **outside** every field
and every solution: `eq:Rproduct` and `eq:tame` write `C_m`, `C_k`, `C`, which
depend only on the integer order and on the fixed domain `R³` and norm
conventions — not on the field, its support, or its frequency support. -/
structure TameProductAPI where
  /-- `appendix-a-local-theory.tex:10-11` eq:Rproduct, the constant `C_m` of the
  tame product at integer order `m ≥ 2`.  Total in `m`; only `2 ≤ m` is
  constrained below. -/
  C : ℕ → ℝ
  /-- `appendix-a-local-theory.tex:10` "`≤ C_m(...)`": the constants are finite
  and positive. -/
  C_pos : ∀ m : ℕ, 0 < C m
  /-- `appendix-a-local-theory.tex:16` eq:algebra, the constant `C_k` of the
  algebra bound at integer order `k ≥ 3`.  Kept separate from `C` because the
  manuscript derives it from `eq:Rproduct` and monotonicity, so the two need not
  be equal. -/
  Calg : ℕ → ℝ
  /-- Positivity of `Calg`. -/
  Calg_pos : ∀ k : ℕ, 0 < Calg k
  /-- `appendix-a-local-theory.tex:17-18` eq:tame, the constant `C_k` of
  `‖u⊗u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}`.  Separate again: eq:tame keeps the low
  factor at order two where eq:algebra does not. -/
  Ctame : ℕ → ℝ
  /-- Positivity of `Ctame`. -/
  Ctame_pos : ∀ k : ℕ, 0 < Ctame k
  /-- `appendix-a-local-theory.tex:12` eq:Rproduct, second clause: the single
  constant `C` of `‖v‖_∞ ≤ C‖v‖_{H²}`.  It carries no order index because the
  order is fixed at two; `04-whole-space.tex:53` and
  `research/section4/STATEMENTS.md:1121-1122` use exactly this constant. -/
  Cinfty : ℝ
  /-- Positivity of `Cinfty`. -/
  Cinfty_pos : 0 < Cinfty

  /-- `01-introduction.tex:103` "For vectors and tensors we sum the squared
  component norms": the vector quantity of `Contracts/V1/Data.lean:189` is the
  Euclidean assembly of the three scalar quantities of `scalarSobolevENorm`.
  This is the clause that makes the componentwise argument of
  `appendix-a-local-theory.tex:50` connect the scalar statement `eq:Rproduct`
  to every vector and tensor statement below; without it the two carriers are
  unrelated.  It is an identity, not an estimate, because both sides are the
  same `PiLp 2` norm of the same datum
  (`Data.RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)`). -/
  componentSobolevENorm :
    ∀ (s : ℝ) (z : SpatialField),
      sobolevENorm s z ^ (2 : ℝ) =
        ∑ i : Fin 3, scalarSobolevENorm s (fun x => z x i) ^ (2 : ℝ)

  /-- `02-preliminaries.tex:12` eq:Rinitial and `:29-30`: every smooth `H^∞`
  field is admissible at every integer order.  This is the identification field
  that makes all clauses below apply to the objects Section 4 actually holds —
  the initial velocities of `X_R`, the force slices of `F_R`, and the velocity
  slices of `Data.ClassicalSolutionR` — none of which is presented as a datum.
  `Contracts/V1/Data.lean:495` already puts an `H^m` datum on such a field for
  every `m`; the content added here is genuine `L²` membership of the physical
  field, which `Contracts/V1/Data.lean:152-155` names but does not state. -/
  memHInfty_memHm :
    ∀ (m : ℕ) (z : SpatialField), MemHInfty z → MemHmVector m z

  /-- The scalar half of the previous clause: each Euclidean component of a
  smooth `H^∞` field is an admissible scalar, so that `tameProductScalar` can be
  applied componentwise as `appendix-a-local-theory.tex:50` prescribes. -/
  memHInfty_component :
    ∀ (m : ℕ) (z : SpatialField), MemHInfty z →
      ∀ i : Fin 3, MemHmScalar m (fun x => z x i)

  /-- The derivative half: `∂_j` of a smooth `H^∞` field is again admissible at
  every order.  Needed because `eq:Rhigh` (`appendix-a-local-theory.tex:134`)
  and the uniqueness coefficient (`:120`) both estimate derivatives, and
  `MemHInfty` is not visibly closed under `∂_j` at the level of
  `Contracts/V1/Data.lean`. -/
  memHInfty_partialDeriv :
    ∀ (m : ℕ) (z : SpatialField), MemHInfty z →
      ∀ j : Fin 3, MemHmVector m (partialDeriv j z)

  /-- `01-introduction.tex:94-95` with `|ξ_j|⟨ξ⟩^s ≤ ⟨ξ⟩^{s+1}` and
  `∑_j|ξ_j|² = |ξ|²`: `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}`, with constant one.  This is
  the step by which `appendix-a-local-theory.tex:122-123` reads the uniqueness
  coefficient `‖∇u₂‖_∞` against `u₂ ∈ C_tH³`, and by which A04 reads
  `eq:Rhigh`'s `‖∇u‖_{H^m}` against `‖u‖_{H^{m+1}}`.  Stated at real `s ≥ 0`
  because both integer and the half-integer orders of Proposition 4.4 use it;
  `research/A05/Spec.lean` states the companion inequality
  `dotThreeHalvesLeGradientSobolev` at `s = 1/2`. -/
  gradientSobolevENorm_le :
    ∀ (s : ℝ), 0 ≤ s → ∀ v : SpatialField, MemHInfty v →
      gradientSobolevENorm s v ≤ sobolevENorm (s + 1) v

  /-- `appendix-a-local-theory.tex:12` eq:Rproduct, second clause, and `:49-50`
  "Absolute Fourier convergence also proves the `L^∞` estimate": every field of
  `H²(R³;R³)` has a **continuous bounded representative**, whose supremum is at
  most `C‖z‖_{H²}`.

  The representative form is the honest one: `Data.IsSobolevDatum` sees a
  physical field only through Schwartz pairings, so it cannot see a modification
  on a null set, and a pointwise bound on `z` itself would be false for such a
  modification.  `supNorm_le_of_continuous` below removes the representative
  again on the continuous fields Section 4 applies this to.

  This is also the clause that pins "bounded representative" in the task title,
  and the one the whole in-tree route already produces:
  `NSFormalization.Paper3.sobolevBoundedRepresentative`
  (`formalization/NSFormalization/Paper3/SobolevBoundedRepresentative.lean:34`)
  lands in `BoundedContinuousFunction Space ℂ`. -/
  boundedRepresentative :
    ∀ z : SpatialField, MemHmVector 2 z →
      ∃ w : SpatialField,
        Continuous w ∧ (∀ᵐ x ∂(volume : Measure Space), w x = z x) ∧
          ∀ x : Space, ‖w x‖ₑ ≤ ENNReal.ofReal Cinfty * sobolevENorm 2 z

  /-- `appendix-a-local-theory.tex:12` eq:Rproduct, second clause, as an
  essential-supremum bound: `‖z‖_{L^∞(R³)} ≤ C‖z‖_{H²}`.  This is
  `research/section4/STATEMENTS.md:261-262`'s `⟪D01:normLinfty⟫` clause verbatim,
  and the form in which a bound on `‖·‖_∞` composes with the `L^p` machinery of
  `Contracts/V1/Data.lean`. -/
  eLpNormTop_le :
    ∀ z : SpatialField, MemHmVector 2 z →
      eLpNorm z ⊤ volume ≤ ENNReal.ofReal Cinfty * sobolevENorm 2 z

  /-- `04-whole-space.tex:53`, the decisive sentence of Theorem 4.2: "An
  extension through `T` would be bounded in `C_tH²` on a neighborhood of `T`,
  hence bounded in `L^∞_x` by `eq:Rproduct`, contradicting the blowup of
  `U_ε`."  The contradiction is with
  `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞`, a statement about the **actual pointwise
  values** of a smooth field, so the bound is needed at every point and not
  merely almost everywhere.  Two continuous fields that agree almost everywhere
  on `R³` agree everywhere, so this is `boundedRepresentative` with the
  representative discharged; it is a separate field so that R42 never has to
  perform that step.

  `research/section4/STATEMENTS.md:314` and `:1120-1122` identify this as the
  input that requires the missing DAG edge `A03 → R42`. -/
  supNorm_le_of_continuous :
    ∀ z : SpatialField, Continuous z → MemHmVector 2 z →
      ∀ x : Space, ‖z x‖ₑ ≤ ENNReal.ofReal Cinfty * sobolevENorm 2 z

  /-- `appendix-a-local-theory.tex:120` `‖∇u₂‖_∞`, the coefficient of the
  difference-energy inequality that Grönwall integrates, and `:122-123` "The
  coefficient is bounded on compact common intervals, since `u₂ ∈ C_tH³`".
  It is `supNorm_le_of_continuous` applied componentwise to the three fields
  `∂_ju₂` (`:50` "The argument applies componentwise to vectors and tensors"),
  reassembled in the Frobenius norm of `gradientTensor`; composing with
  `gradientSobolevENorm_le` at `s = 2` turns the right-hand side into
  `C‖u₂‖_{H³}`, which is the form the manuscript quotes. -/
  gradientSupNorm_le :
    ∀ v : SpatialField, MemHInfty v →
      ∀ x : Space,
        ‖gradientTensor v x‖ₑ ≤ ENNReal.ofReal Cinfty * gradientSobolevENorm 2 v

  /-- `appendix-a-local-theory.tex:9-11` eq:Rproduct, first clause, exactly as
  written: for every integer `m ≥ 2`,
  `‖vw‖_{H^m} ≤ C_m(‖v‖_{H²}‖w‖_{H^m} + ‖w‖_{H²}‖v‖_{H^m})`,
  where `vw` is the literal pointwise product of two physical scalars.

  Because the left-hand side is `⊤` when the product has no order-`m` datum, a
  finite right-hand side makes this clause assert that `H^m(R³)` is closed under
  multiplication, which is the half of `eq:Rproduct` that the completed
  in-tree product `NSFormalization.Paper3.sobolevProduct`
  (`Paper3/CompleteTameProduct.lean:100`) constructs. -/
  tameProductScalar :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : Space → ℝ,
      MemHmScalar m a → MemHmScalar m b →
        scalarSobolevENorm (m : ℝ) (fun x => a x * b x) ≤
          ENNReal.ofReal (C m) *
            (scalarSobolevENorm 2 a * scalarSobolevENorm (m : ℝ) b +
              scalarSobolevENorm 2 b * scalarSobolevENorm (m : ℝ) a)

  /-- `appendix-a-local-theory.tex:9-11` with `:50` "The argument applies
  componentwise to vectors and tensors": the same bound for the product of a
  physical scalar with a physical three-vector, `x ↦ a(x)·w(x)`.  This is the
  shape every Section 4 nonlinearity has — the columns of `u ⊗ u` are
  `u_j · u`, and the summands of `(u·∇)v` are `u_j · ∂_jv` — so it, not the
  scalar clause, is what `outerProductTame` and `advectionTame` specialize.

  The dimensional factor from summing the three Euclidean components is absorbed
  into `C m`, which the manuscript allows: `C_m` depends only on the order and
  the fixed domain. -/
  tameProductVector :
    ∀ m : ℕ, 2 ≤ m → ∀ (a : Space → ℝ) (w : SpatialField),
      MemHmScalar m a → MemHmVector m w →
        sobolevENorm (m : ℝ) (fun x => a x • w x) ≤
          ENNReal.ofReal (C m) *
            (scalarSobolevENorm 2 a * sobolevENorm (m : ℝ) w +
              sobolevENorm 2 w * scalarSobolevENorm (m : ℝ) a)

  /-- `appendix-a-local-theory.tex:14-16` eq:algebra: "In particular, for
  integers `k ≥ 3`, `‖vw‖_{H^k} ≤ C_k‖v‖_{H^k}‖w‖_{H^k}`."  The manuscript
  derives it from eq:Rproduct and `‖·‖_{H²} ≤ ‖·‖_{H^k}`; it is kept as its own
  field because the difference bound below and A01's contraction argument quote
  the symmetric form. -/
  algebraProductScalar :
    ∀ k : ℕ, 3 ≤ k → ∀ a b : Space → ℝ,
      MemHmScalar k a → MemHmScalar k b →
        scalarSobolevENorm (k : ℝ) (fun x => a x * b x) ≤
          ENNReal.ofReal (Calg k) *
            (scalarSobolevENorm (k : ℝ) a * scalarSobolevENorm (k : ℝ) b)

  /-- `appendix-a-local-theory.tex:17-18` eq:tame:
  `‖u ⊗ u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` for integers `k ≥ 3`.  This is the
  clause A04 consumes: `eq:Rhigh` (`:132-137`) is obtained by pairing the
  equation with `u` in `H^m`, integrating the nonlinear divergence by parts, and
  bounding `|⟨∇·(u⊗u), u⟩_{H^m}| ≤ ‖u⊗u‖_{H^m}‖∇u‖_{H^m}`; only the first
  factor is Lemma A.1's, and it is exactly this field.

  The tensor is `u ⊗ u` in the nine-entry Frobenius norm of
  `columnsSobolevENorm`, per `01-introduction.tex:103`. -/
  outerProductTame :
    ∀ k : ℕ, 3 ≤ k → ∀ u : SpatialField, MemHInfty u →
      outerSobolevENorm (k : ℝ) u u ≤
        ENNReal.ofReal (Ctame k) * (sobolevENorm 2 u * sobolevENorm (k : ℝ) u)

  /-- `appendix-a-local-theory.tex:51-52` "and factorization gives the
  corresponding product difference bound", used at
  `paper/originals/local/paper_3_whole_space.tex:157` and quantified at `:192`
  ("its difference by the same factor times
  `(‖u‖_{C_tH³}+‖v‖_{C_tH³})‖u−v‖_{C_tH³}`"):
  `‖u⊗u − v⊗v‖_{H^k} ≤ C_k(‖u‖_{H^k}+‖v‖_{H^k})‖u−v‖_{H^k}`.

  The factorization is `u⊗u − v⊗v = (u−v)⊗u + v⊗(u−v)`, so the constant is
  eq:algebra's.  This is the estimate the mild contraction and the uniqueness
  argument of `prop:local` run on; A01/A02 consume it. -/
  outerProductDifference :
    ∀ k : ℕ, 3 ≤ k → ∀ u v : SpatialField, MemHInfty u → MemHInfty v →
      outerDiffSobolevENorm (k : ℝ) u v ≤
        ENNReal.ofReal (Calg k) *
          ((sobolevENorm (k : ℝ) u + sobolevENorm (k : ℝ) v) *
            sobolevENorm (k : ℝ) (diffField u v))

  /-- `01-introduction.tex:83` eq:NS's nonlinearity `(u·∇)u`, in the bilinear
  form `(u·∇)v`, estimated by eq:Rproduct applied componentwise to the summands
  `u_j·∂_jv` (`appendix-a-local-theory.tex:9-11` with `:50`):
  `‖(u·∇)v‖_{H^m} ≤ C_m(‖u‖_{H²}‖∇v‖_{H^m} + ‖∇v‖_{H²}‖u‖_{H^m})`.

  The manuscript's own energy identity `eq:Rhigh` goes through `u ⊗ u` and the
  divergence form, so this field is not used by `eq:Rhigh`; it is here because
  `02-preliminaries.tex:81` eq:projected and
  `Data.ClassicalSolutionR.momentum` (`Contracts/V1/Data.lean:624`) both state
  the equation with `advection`, so a consumer that never converts to divergence
  form still needs the nonlinearity's `H^m` bound.  The conversion itself,
  `∇·(u⊗u) = (u·∇)u` for divergence-free smooth `u`, is A01's unit E1
  (`research/A01/COMPARISON.md:190`) and is deliberately not asserted here.

  As in `tameProductVector`, the factor of three from summing over `j` is
  absorbed into `C m`. -/
  advectionTame :
    ∀ m : ℕ, 2 ≤ m → ∀ u v : SpatialField, MemHInfty u → MemHInfty v →
      sobolevENorm (m : ℝ) (advectionOf u v) ≤
        ENNReal.ofReal (C m) *
          (sobolevENorm 2 u * gradientSobolevENorm (m : ℝ) v +
            gradientSobolevENorm 2 v * sobolevENorm (m : ℝ) u)

end BlowupDensity.A03.Draft
