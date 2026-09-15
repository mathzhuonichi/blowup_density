import Contracts.V1.Data

/-! Stable specification for the **product** clauses of Lemma A.1.

Task `collaboration/tasks/A03.md`, graph node `A03`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:214-223`).  Version 1 fixes the
multiplication half of Lemma A.1, "Sobolev multiplication and embeddings"
(`lem:calculus`, `paper/sections/appendix-a-local-theory.tex:7-27`), on `R³`:

* `eq:Rproduct`, first clause (`:9-11`),
  `‖vw‖_{H^m} ≤ C_m(‖v‖_{H²}‖w‖_{H^m} + ‖w‖_{H²}‖v‖_{H^m})` for integers
  `m ≥ 2`, for a product of two real scalars and for the product of a real
  scalar with a real three-vector (`:50`, "The argument applies componentwise to
  vectors and tensors");
* `eq:algebra` (`:14-16`), `‖vw‖_{H^k} ≤ C_k‖v‖_{H^k}‖w‖_{H^k}` for integers
  `k ≥ 3`;
* `eq:tame` (`:17-18`), `‖u ⊗ u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` for integers
  `k ≥ 3`, with the low factor at order **two** — which is what makes
  `eq:Rhigh`'s continuation criterion an `H²` criterion;
* `:51-52`, "factorization gives the corresponding product difference bound" —
  which the manuscript states **qualitatively only** (the same sentence appears at
  `paper/originals/local/paper_3_whole_space.tex:156`; no inequality of this shape
  is displayed anywhere under `paper/`), so the quantified form registered below
  is *derived*, by the factorization `u⊗u − v⊗v = (u−v)⊗u + v⊗(u−v)` together
  with `eq:algebra`;
* the `H^m` bound for the bilinear advection `(u·∇)v` of `01-introduction.tex:83`
  eq:NS, for smooth fields with square-integrable jets.

## Consumers

* **A04** through `eq:Rhigh` (`appendix-a-local-theory.tex:132-137`): the
  nonlinear term of the order-`m` energy identity is bounded by `eq:Rproduct`
  applied to `u ⊗ u`, i.e. by `outerProductTame`, followed by Cauchy–Schwarz
  against `‖∇u‖_{H^m}`.  The Cauchy–Schwarz step, the integration by parts and
  the Grönwall are A04's, not this contract's.
* **A01/A02** through the mild contraction and the uniqueness argument of
  `prop:local` (`:110-125`): `outerProductTame` and `outerProductDifference`,
  both stated on the `H^k` class `MemHmVector k` so that they apply to two
  arbitrary elements of the ball of `C([0,τ];H³)` on which that contraction runs.

## Out of scope, and asserted nowhere below

* Every **embedding** clause of `lem:calculus`.  `‖v‖_∞ ≤ C‖v‖_{H²}`
  (`eq:Rproduct`, second clause, `:12`) is registered separately as
  `A03.bounded_representative`
  (`verification/Contracts/V1/BoundedRepresentative.lean`); `H¹ ↪ L⁶` (`:20`)
  and `eq:embeddings` (`:22-26`) belong to A05
  (`verification/Contracts/V1/GradientL6.lean`).
* The **torus** half of `lem:calculus` (`:8`, "either domain").  Everything below
  is whole space only.
* The order shift `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}`, the uniqueness coefficient
  `‖∇u₂‖_∞` of `:120-123`, and the identity `∇·(u⊗u) = (u·∇)u` for
  divergence-free smooth `u` (A01 unit E1).
* Every clause of the accepted draft `research/A03/Spec.lean` whose hypothesis is
  the **datum** form `Data.MemHInfty`.  Getting physical `L²` membership out of
  `MemHInfty` is the open direction of D01 unit L2
  (`Contracts/V1/Data.lean:487-491`, `research/D01/RECONCILIATION.md:153`);
  `formalization/NSFormalization/Section4/D01/SmoothDatum.lean` proves the other
  direction only.  `Spec.lean` has four such clauses, and **two** of them —
  `memHInfty_memHm` (`:324`) and `advectionTame` (`:564`) — are collected,
  unproved and **unregistered**, in `UnprovedTameProductObligations` at the end
  of this file, together with the exact componentwise norm identity.  The other
  two, `memHInfty_component` (`:330`) and `memHInfty_partialDeriv` (`:339`), are
  deliberately **not** restated there: each is a one-step corollary of
  `memHInfty_memHm` and a field that *is* registered here
  (`scalarSobolevENorm_component_le` and `smoothJets_partialDeriv` respectively),
  so collecting them would double-count one debt.
  `research/A03/ATTEMPTS_TAME.md` records why.

## Conventions

* **Fourier.**  The manuscript's unitary angular transform
  `ẑ(ξ) = (2π)^{-3/2}∫exp(-i x·ξ)z(x)dx` (`01-introduction.tex:91`), carried by
  `Data.IsSobolevDatum` and by `IsScalarSobolevDatum` below.  Mathlib's
  cycles-convention `𝓕` never appears in a statement of this file.  The
  implementation's product theory is proved in the cycles convention and
  transported; every constant therefore carries an explicit power of `2π`, which
  is invisible here because the constants are opaque structure fields.
  `research/A03/ATTEMPTS_TAME.md` records the bookkeeping.
* **Vectors and tensors.**  `01-introduction.tex:103`, "for vectors and tensors
  we sum the squared component norms": `Data.sobolevENorm` for a three-vector and
  the Euclidean assembly `columnsSobolevENorm` of the three column norms for a
  `3×3` tensor, i.e. the full nine-entry Frobenius quantity.
* **Physical fields.**  Every clause is about a physical field
  `Data.SpatialField = Space → Space` or a physical scalar `Space → ℝ`, so the
  product is the literal pointwise product and no separate "the completed product
  is multiplication" identification is needed: that identification is built into
  the shape of the statement.
* **Totalization.**  Every norm is `ℝ≥0∞`-valued and none is routed through
  `.toReal`.  `Data.sobolevENorm` is an infimum over data and
  `Contracts/V1/Data.lean:148-155` records that it totalizes to a junk `0` on a
  slice pairing integrably with no Schwartz test; `MemHmScalar`/`MemHmVector`
  add the `MemLp _ 2` hypothesis that excludes this, and it is also exactly the
  local integrability the implementation's identification of the datum with the
  field needs.
* **Constants.**  All constants are structure fields, hence quantified *outside*
  every field: `appendix-a-local-theory.tex:10` fixes `C_m`, `C_k`, `C` to depend
  only on the integer order and the fixed domain `R³` — never on the field, its
  support or its frequency support.  This is the task's "with constants
  independent of support".  `Cdiff` is a separate field from `Calg`, where the
  manuscript writes one symbol for both; separate constants are no weaker.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.TameProduct

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (angularRealization)
open NSFormalization.Source.RealSobolev (FourierData RealSobolevHilbert)
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. The scalar carrier

`Contracts.V1.Data` supplies `IsSobolevDatum` and `sobolevENorm` for real
**three-vector** fields only; `eq:Rproduct`'s `vw` is a product of scalars.  The
two definitions below are the scalar case of the same pairing — literally one
component of `Data.IsSobolevDatum`, since `RealSobolevHilbert s` is the component
type of `Data.RealVectorSobolev s`. -/

/-- `01-introduction.tex:91,94`: `A` is *the* order-`s` angular real Sobolev
datum of the physical scalar `a`, in the sense that the distribution it realizes
pairs with every Schwartz test exactly as `a` does.  The same totalization caveat
as `Data.IsSobolevDatum` applies and is handled the same way, by `MemHmScalar`. -/
def IsScalarSobolevDatum (s : ℝ) (a : Space → ℝ) (A : RealSobolevHilbert s) : Prop :=
  ∀ ψ : SchwartzMap Space ℂ,
    angularRealization s (A : FourierData) ψ = ∫ x : Space, ψ x * ((a x : ℝ) : ℂ)

/-- `01-introduction.tex:94`, `‖a‖_{H^s(R³)}` for a physical **scalar** field:
the norm of the order-`s` datum, and `⊤` when `a` has none, the empty infimum in
`ℝ≥0∞` being `⊤`.  Exactly `Data.sobolevENorm` with `Fin 3` replaced by a
point. -/
def scalarSobolevENorm (s : ℝ) (a : Space → ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : RealSobolevHilbert s // IsScalarSobolevDatum s a A}, ‖A.1‖ₑ

/-- The class Lemma A.1 is applied to at integer order `m`: a physical real
three-vector field that is genuinely square integrable and has a finite
order-`m` norm.  `02-preliminaries.tex:29-30` is the manuscript's version. -/
def MemHmVector (m : ℕ) (z : SpatialField) : Prop :=
  MemLp z 2 volume ∧ sobolevENorm (m : ℝ) z ≠ ⊤

/-- The scalar counterpart of `MemHmVector`, for the factors of `eq:Rproduct`'s
`vw`. -/
def MemHmScalar (m : ℕ) (a : Space → ℝ) : Prop :=
  MemLp a 2 volume ∧ scalarSobolevENorm (m : ℝ) a ≠ ⊤

/-! ## 2. The bilinear forms and the tensor norm -/

/-- The time-independent lift of a spatial field, so that the pinned upstream
`spatialDerivative` can be reused verbatim on a fixed-time slice.  Same device as
`Data.IsSolenoidal` (`Contracts/V1/Data.lean:504`). -/
def lift (v : SpatialField) : SpaceTimeField := fun z => v z.2

/-- `appendix-a-local-theory.tex:50`, "The argument applies componentwise": the
`j`-th partial derivative of a spatial field, again a spatial field. -/
def partialDeriv (j : Fin 3) (v : SpatialField) : SpatialField :=
  fun x => spatialDerivative (lift v) 0 x (coordinateVector j)

/-- `01-introduction.tex:83` eq:NS and `02-preliminaries.tex:81` eq:projected:
the bilinear advection `(u·∇)v`, as a spatial field.  On the diagonal it is the
pinned upstream nonlinearity `advection` on the time-independent lift. -/
def advectionOf (u v : SpatialField) : SpatialField :=
  fun x => spatialDerivative (lift v) 0 x (u x)

/-- `appendix-a-local-theory.tex:17` eq:tame: the `j`-th column of the tensor
`u ⊗ v`, i.e. the vector field `x ↦ u_j(x)·v(x)`. -/
def outerColumn (u v : SpatialField) (j : Fin 3) : SpatialField := fun x => (u x j) • v x

/-- Pointwise difference of two spatial fields. -/
def diffField (u v : SpatialField) : SpatialField := fun x => u x - v x

/-- `01-introduction.tex:103`, "for vectors and tensors we sum the squared
component norms": the order-`s` Sobolev norm of a `3×3` tensor field presented by
its three columns.  `Data.sobolevENorm` already sums the three Euclidean
components of each column, so this is the full nine-entry quantity. -/
def columnsSobolevENorm (s : ℝ) (T : Fin 3 → SpatialField) : ℝ≥0∞ :=
  (∑ j : Fin 3, sobolevENorm s (T j) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `appendix-a-local-theory.tex:17` eq:tame, `‖u ⊗ v‖_{H^s}`. -/
def outerSobolevENorm (s : ℝ) (u v : SpatialField) : ℝ≥0∞ :=
  columnsSobolevENorm s (outerColumn u v)

/-- `appendix-a-local-theory.tex:51-52`, `‖u⊗u − v⊗v‖_{H^s}`. -/
def outerDiffSobolevENorm (s : ℝ) (u v : SpatialField) : ℝ≥0∞ :=
  columnsSobolevENorm s (fun j => diffField (outerColumn u u j) (outerColumn v v j))

/-- `appendix-a-local-theory.tex:134`, `‖∇v‖_{H^s}`: the tensor norm of the
gradient.  Numerically the same quantity as `research/A05/Spec.lean`'s
`tensorSobolevENorm`, `(∑_j ‖∂_jv‖²_{H^s})^{1/2}`. -/
def gradientSobolevENorm (s : ℝ) (v : SpatialField) : ℝ≥0∞ :=
  columnsSobolevENorm s (fun j => partialDeriv j v)

/-- The jet form of `02-preliminaries.tex:12` eq:Rinitial's `H^∞(R³;R³)`: smooth,
with every Fréchet jet square integrable.  Field for field the vendor's
`EulerLpTranslation.SmoothL2Field`, written out here because a specification may
not import an implementation module, and the same spelling as
`Contracts.V1.BoundedRep.SmoothSquareIntegrableJets` and
`Contracts.V1.SmoothSquareIntegrableJets`.

This is **not** definitionally `Data.MemHInfty`, which is the datum form.
`Section4/D01/SmoothDatum.lean` proves `SmoothJets z → Data.MemHInfty z`; the
converse is open, which is why the advection clause below is stated here rather
than on `MemHInfty` (see the module docstring and
`UnprovedTameProductObligations`). -/
def SmoothJets (v : SpatialField) : Prop :=
  ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume

/-! ## 3. The contract -/

/-- The product clauses of Lemma A.1 (`lem:calculus`,
`paper/sections/appendix-a-local-theory.tex:7-27`) on `R³`, at the datum level of
`Contracts/V1/Data.lean`, in the form A04, A01 and A02 consume them. -/
structure TameProductAPI where
  /-- `appendix-a-local-theory.tex:10-11` eq:Rproduct, the constant `C_m` of the
  tame product at integer order `m ≥ 2`.  One constant serves both the scalar and
  the scalar-times-vector clause, as the manuscript's `C_m` does.  Total in `m`;
  only `2 ≤ m` is constrained below. -/
  C : ℕ → ℝ
  /-- `appendix-a-local-theory.tex:10`, "`≤ C_m(...)`": the constants are finite
  and positive, so the bounds below are genuine estimates. -/
  C_pos : ∀ m : ℕ, 0 < C m
  /-- `appendix-a-local-theory.tex:16` eq:algebra, the constant `C_k` at integer
  order `k ≥ 3`.  Kept separate from `C` because the manuscript *derives* it from
  eq:Rproduct and monotonicity, so the two need not be equal. -/
  Calg : ℕ → ℝ
  /-- Positivity of `Calg`. -/
  Calg_pos : ∀ k : ℕ, 0 < Calg k
  /-- `appendix-a-local-theory.tex:17-18` eq:tame, the constant `C_k` of
  `‖u⊗u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}`.  Separate again: eq:tame keeps the low
  factor at order two where eq:algebra does not. -/
  Ctame : ℕ → ℝ
  /-- Positivity of `Ctame`. -/
  Ctame_pos : ∀ k : ℕ, 0 < Ctame k
  /-- `appendix-a-local-theory.tex:51-52`, the constant of the product difference
  bound.  The manuscript writes eq:algebra's symbol here; a separate field is no
  weaker, since both are quantified outside every field. -/
  Cdiff : ℕ → ℝ
  /-- Positivity of `Cdiff`. -/
  Cdiff_pos : ∀ k : ℕ, 0 < Cdiff k
  /-- The constant of the advection bound, `eq:Rproduct` summed over the three
  summands `u_j·∂_jv`. -/
  Cadv : ℕ → ℝ
  /-- Positivity of `Cadv`. -/
  Cadv_pos : ∀ m : ℕ, 0 < Cadv m

  /-- `01-introduction.tex:103`: each Euclidean component of a three-vector field
  is dominated by the field.  With `sobolevENorm_le_sum_components` this is the
  clause that makes the componentwise argument of
  `appendix-a-local-theory.tex:50` connect the scalar statement `eq:Rproduct` to
  the vector and tensor statements below; without the pair, the two carriers are
  unrelated.  No hypothesis is needed: the right-hand side is `⊤` when `z` has no
  order-`s` datum.

  The accepted draft `research/A03/Spec.lean:311` asks for the exact identity
  `‖z‖²_{H^s} = ∑_i ‖z_i‖²_{H^s}`; only these two inequalities are proved, and
  the identity stays in `UnprovedTameProductObligations`. -/
  scalarSobolevENorm_component_le :
    ∀ (s : ℝ) (z : SpatialField) (i : Fin 3),
      scalarSobolevENorm s (fun x => z x i) ≤ sobolevENorm s z
  /-- `01-introduction.tex:103` in the other direction, with the dimensional
  factor implicit in the sum over the three components. -/
  sobolevENorm_le_sum_components :
    ∀ (s : ℝ) (z : SpatialField),
      sobolevENorm s z ≤ ∑ i : Fin 3, scalarSobolevENorm s (fun x => z x i)

  /-- `02-preliminaries.tex:12` eq:Rinitial and `:29-30`: a smooth field with
  square-integrable jets is admissible at every integer order.  This is the
  identification field by which Section 4's smooth objects enter the clauses
  below; it runs through
  `NSFormalization.Section4.D01.sobolevENorm_ne_top_of_contDiff_memLp`, the jets
  ⇒ datum direction of D01 unit L2, which holds at every real order with no
  compact-support hypothesis. -/
  smoothJets_memHmVector :
    ∀ (m : ℕ) (z : SpatialField), SmoothJets z → MemHmVector m z
  /-- The scalar half of the previous clause, so that the scalar tame product can
  be applied componentwise as `appendix-a-local-theory.tex:50` prescribes. -/
  smoothJets_memHmScalar :
    ∀ (m : ℕ) (z : SpatialField), SmoothJets z →
      ∀ i : Fin 3, MemHmScalar m (fun x => z x i)
  /-- The derivative half: `∂_j` of a smooth field with square-integrable jets is
  again such a field, hence admissible at every order.  Needed because
  `eq:Rhigh` (`:134`) and the advection clause both estimate derivatives. -/
  smoothJets_partialDeriv :
    ∀ (z : SpatialField), SmoothJets z → ∀ j : Fin 3, SmoothJets (partialDeriv j z)

  /-- **`appendix-a-local-theory.tex:9-11` eq:Rproduct, first clause**, exactly as
  written: for every integer `m ≥ 2`,
  `‖ab‖_{H^m} ≤ C_m(‖a‖_{H²}‖b‖_{H^m} + ‖b‖_{H²}‖a‖_{H^m})`,
  where `ab` is the literal pointwise product of two physical scalars.

  Because the left-hand side is `⊤` when the product has no order-`m` datum, a
  finite right-hand side also asserts that `H^m(R³)` is closed under
  multiplication — the half of `eq:Rproduct` that the completed in-tree product
  constructs. -/
  tameProductScalar :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : Space → ℝ,
      MemHmScalar m a → MemHmScalar m b →
        scalarSobolevENorm (m : ℝ) (fun x => a x * b x) ≤
          ENNReal.ofReal (C m) *
            (scalarSobolevENorm 2 a * scalarSobolevENorm (m : ℝ) b +
              scalarSobolevENorm 2 b * scalarSobolevENorm (m : ℝ) a)

  /-- **`appendix-a-local-theory.tex:9-11` with `:50`**: the same bound for the
  product of a physical scalar with a physical three-vector, `x ↦ a(x)·w(x)`.
  This is the shape every Section 4 nonlinearity has — the columns of `u ⊗ u` are
  `u_j·u`, the summands of `(u·∇)v` are `u_j·∂_jv` — so it, not the scalar
  clause, is what the tensor clauses below specialize.  The dimensional factor
  from summing the three Euclidean components is absorbed into `C m`, which the
  manuscript allows. -/
  tameProductVector :
    ∀ m : ℕ, 2 ≤ m → ∀ (a : Space → ℝ) (w : SpatialField),
      MemHmScalar m a → MemHmVector m w →
        sobolevENorm (m : ℝ) (fun x => a x • w x) ≤
          ENNReal.ofReal (C m) *
            (scalarSobolevENorm 2 a * sobolevENorm (m : ℝ) w +
              sobolevENorm 2 w * scalarSobolevENorm (m : ℝ) a)

  /-- **`appendix-a-local-theory.tex:14-16` eq:algebra**: "In particular, for
  integers `k ≥ 3`, `‖vw‖_{H^k} ≤ C_k‖v‖_{H^k}‖w‖_{H^k}`."  The implementation
  derives it, as the manuscript does, from eq:Rproduct and
  `‖·‖_{H²} ≤ ‖·‖_{H^k}`, and in fact proves it for every `k ≥ 2`; `3 ≤ k` is
  registered because that is what the manuscript states. -/
  algebraProductScalar :
    ∀ k : ℕ, 3 ≤ k → ∀ a b : Space → ℝ,
      MemHmScalar k a → MemHmScalar k b →
        scalarSobolevENorm (k : ℝ) (fun x => a x * b x) ≤
          ENNReal.ofReal (Calg k) *
            (scalarSobolevENorm (k : ℝ) a * scalarSobolevENorm (k : ℝ) b)

  /-- **`appendix-a-local-theory.tex:17-18` eq:tame**:
  `‖u ⊗ u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` for integers `k ≥ 3`.  This is the
  clause A04 consumes: `eq:Rhigh` (`:132-137`) pairs the equation with `u` in
  `H^m`, integrates the nonlinear divergence by parts and bounds
  `|⟨∇·(u⊗u), u⟩_{H^m}| ≤ ‖u⊗u‖_{H^m}‖∇u‖_{H^m}`; only the first factor is Lemma
  A.1's, and it is exactly this field.  The tensor is measured in the nine-entry
  Frobenius norm of `columnsSobolevENorm`.

  *Hypothesis.*  `MemHmVector k`, not a smoothness class: `eq:tame` holds on
  `H^k`, and the mild contraction of `prop:local`
  (`appendix-a-local-theory.tex:110-116`) runs on the ball of `C([0,τ];H³)`,
  whose elements are `H³` and not `H^∞`.  Only pointwise products occur, so no
  differentiability is needed and none is assumed. -/
  outerProductTame :
    ∀ k : ℕ, 3 ≤ k → ∀ u : SpatialField, MemHmVector k u →
      outerSobolevENorm (k : ℝ) u u ≤
        ENNReal.ofReal (Ctame k) * (sobolevENorm 2 u * sobolevENorm (k : ℝ) u)

  /-- **`appendix-a-local-theory.tex:51-52`**, "and factorization gives the
  corresponding product difference bound":
  `‖u⊗u − v⊗v‖_{H^k} ≤ C_k(‖u‖_{H^k}+‖v‖_{H^k})‖u−v‖_{H^k}`.

  *Provenance.*  The manuscript's claim is **qualitative**: `:51-52`, and the same
  sentence at `paper/originals/local/paper_3_whole_space.tex:156`, assert that the
  factorization "gives the corresponding difference estimate" and display no
  inequality; no quantified bound of this shape occurs anywhere under `paper/`.
  The displayed form above is therefore **derived**, not quoted — by the
  factorization `u⊗u − v⊗v = (u−v)⊗u + v⊗(u−v)` together with `eq:algebra`, which
  is exactly how the Lean proof runs.  Because the manuscript names no constant
  here, `Cdiff` is a field of its own rather than eq:algebra's `C_k`.

  This is the estimate the mild contraction and the uniqueness argument of
  `prop:local` (`:110-125`) run on, and it is stated at `MemHmVector k` for the
  same reason as `outerProductTame`. -/
  outerProductDifference :
    ∀ k : ℕ, 3 ≤ k → ∀ u v : SpatialField, MemHmVector k u → MemHmVector k v →
      outerDiffSobolevENorm (k : ℝ) u v ≤
        ENNReal.ofReal (Cdiff k) *
          ((sobolevENorm (k : ℝ) u + sobolevENorm (k : ℝ) v) *
            sobolevENorm (k : ℝ) (diffField u v))

  /-- **The `H^m` bound for the advection `(u·∇)v`**, `eq:Rproduct` applied
  componentwise to the summands `u_j·∂_jv` (`appendix-a-local-theory.tex:9-11`
  with `:50`):
  `‖(u·∇)v‖_{H^m} ≤ C_m(‖u‖_{H²}‖∇v‖_{H^m} + ‖∇v‖_{H²}‖u‖_{H^m})`.

  The manuscript's own energy identity `eq:Rhigh` goes through `u ⊗ u` and the
  divergence form, so this field is not used by `eq:Rhigh`; it is here because
  `02-preliminaries.tex:81` eq:projected and `Data.ClassicalSolutionR.momentum`
  (`Contracts/V1/Data.lean:624`) both state the equation with `advection`, so a
  consumer that never converts to divergence form still needs the
  nonlinearity's `H^m` bound.  The conversion `∇·(u⊗u) = (u·∇)u` is A01's unit
  E1 and is deliberately not asserted here.

  *Hypothesis.*  `SmoothJets`, not `MemHmVector`: `advectionOf u v` is built from
  the classical `spatialDerivative` of `v`, which `MemHmVector` does not make
  meaningful — on a merely-`H^m` field `fderiv` totalizes to `0` off the
  differentiability set.  `research/A03/Spec.lean:564` states this clause with
  `Data.MemHInfty` instead; that version is **not** registered, because getting
  `MemLp` out of `MemHInfty` is the open direction of D01 unit L2.  It is kept,
  unproved, in `UnprovedTameProductObligations`. -/
  smoothJets_advectionTame :
    ∀ m : ℕ, 2 ≤ m → ∀ u v : SpatialField, SmoothJets u → SmoothJets v →
      sobolevENorm (m : ℝ) (advectionOf u v) ≤
        ENNReal.ofReal (Cadv m) *
          (sobolevENorm 2 u * gradientSobolevENorm (m : ℝ) v +
            gradientSobolevENorm 2 v * sobolevENorm (m : ℝ) u)

/-! ## 4. Deliberately **not** registered

The three obligations below are stated in the accepted draft
`research/A03/Spec.lean` and are **not** proved anywhere in this repository.  This
structure is never instantiated, never appears in `verification/contracts.json`,
and no acceptance test mentions it; it exists so that the gap is written down in
the same place as the clauses that were discharged, in the manuscript's own
form and without weakening.  `research/A03/ATTEMPTS_TAME.md` records what was
tried. -/
structure UnprovedTameProductObligations where
  /-- The constant of the advection clause below.  It is a **field of the
  structure**, hence quantified outside every velocity — `Spec.lean:564` uses
  `TameProductAPI`'s own order-indexed `C m`, and
  `appendix-a-local-theory.tex:10` fixes the constant to the integer order and
  the fixed domain `R³`.  Recording the debt with an inner `∃ C` would make it
  weaker than the obligation it stands for, by letting the constant depend on
  `u` and `v`. -/
  Cadv : ℕ → ℝ
  /-- Positivity of `Cadv`, as in `TameProductAPI`. -/
  Cadv_pos : ∀ m : ℕ, 0 < Cadv m
  /-- `research/A03/Spec.lean:311`, `01-introduction.tex:103`: the vector
  quantity is the *exact* Euclidean assembly of the three scalar quantities, not
  merely bounded above and below by it.  Both sides are the same `PiLp 2` norm of
  the same datum, so this is an identity; proving it needs the squared-norm
  identity transported to `ℝ≥0∞` through the datum infimum.  Only the two
  inequalities `scalarSobolevENorm_component_le` and
  `sobolevENorm_le_sum_components` are registered, and they are what every clause
  of `TameProductAPI` uses. -/
  componentSobolevENorm :
    ∀ (s : ℝ) (z : SpatialField),
      sobolevENorm s z ^ (2 : ℝ) =
        ∑ i : Fin 3, scalarSobolevENorm s (fun x => z x i) ^ (2 : ℝ)
  /-- `research/A03/Spec.lean:324`: the **datum** form of the admissibility
  instance.  `Data.MemHInfty` (`Contracts/V1/Data.lean:495`) gives `ContDiff` and
  an order-`m` datum at every `m`; what is missing is genuine `L²` membership of
  the physical field, i.e. the datum ⇒ jet direction of D01 unit L2, recorded as
  open at `research/D01/RECONCILIATION.md:153`.  `smoothJets_memHmVector` is the
  registered substitute and is strictly weaker, since
  `Section4/D01/SmoothDatum.lean` proves `SmoothJets z → Data.MemHInfty z` and
  not the converse. -/
  memHInfty_memHm : ∀ (m : ℕ) (z : SpatialField), MemHInfty z → MemHmVector m z
  /-- `research/A03/Spec.lean:564`: the advection clause with the datum
  hypothesis `Data.MemHInfty` in place of `SmoothJets`.  Blocked by the same open
  direction as `memHInfty_memHm`; `smoothJets_advectionTame` is the registered
  substitute.  The constant is the structure field `Cadv` above, so it is
  quantified outside `u` and `v` exactly as `Spec.lean:564` and
  `appendix-a-local-theory.tex:10` require. -/
  memHInfty_advectionTame :
    ∀ m : ℕ, 2 ≤ m → ∀ u v : SpatialField, MemHInfty u → MemHInfty v →
      sobolevENorm (m : ℝ) (advectionOf u v) ≤
        ENNReal.ofReal (Cadv m) *
          (sobolevENorm 2 u * gradientSobolevENorm (m : ℝ) v +
            gradientSobolevENorm 2 v * sobolevENorm (m : ℝ) u)

end BlowupDensity.Contracts.V1.TameProduct
