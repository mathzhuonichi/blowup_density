import Contracts.V1.Data

/-! Stable specification for the bounded-representative clause of Lemma A.1.

Task `collaboration/tasks/A03.md`, graph node `A03`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:214-223`).  Version 1 fixes
**one** clause of Lemma A.1, "Sobolev multiplication and embeddings"
(`lem:calculus`, `paper/sections/appendix-a-local-theory.tex:7-27`): the second
half of `eq:Rproduct`,

  `‖v‖_∞ ≤ C‖v‖_{H²}`   (`paper/sections/appendix-a-local-theory.tex:12`),

on `R³`, for real three-vector fields, in the two forms Section 4 consumes.

## Consumers

* **Theorem 4.2** (`thm:Rinsert`, `paper/sections/04-whole-space.tex:31-46`),
  the lifespan-`= T` step at `:53`: "An extension through `T` would be bounded
  in `C_tH²` on a neighborhood of `T`, hence bounded in `L^∞_x` by
  `eq:Rproduct`, contradicting the blowup of `U_ε`."  The blowup is stated as a
  `limsup` of an essential supremum (`research/section4/STATEMENTS.md:261-262`
  pins `⟪D01:normLinfty⟫` to `‖·‖_{L^∞(R³)}`, and `:348-350` states the blowup
  as `limsupLeft T (normLinfty ∘ uPert) = ⊤`), so `eLpNormTop_le` below is the
  literal match and is the field that carries the `A03 → R42` edge
  (`research/section4/STATEMENTS.md:314`, `:1120-1122`).
* The uniqueness coefficient `‖∇u₂‖_∞` of
  `paper/sections/appendix-a-local-theory.tex:120-123` ("The coefficient is
  bounded on compact common intervals, since `u₂ ∈ C_tH³`"), through
  `supNorm_le` applied to each `∂_ju₂`.  That consumer needs **two** further
  ingredients this contract does not state: the order shift
  `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}`, and *derivative-closure of the field class* —
  that `∂_jz` is again admissible when `z` is.  Derivative-closure is true and
  routine on both classes below (the order-`n` jet of `fderiv ℝ z` has the same
  pointwise norm as the order-`(n+1)` jet of `z`; lane 019's
  `NSFormalization.Section4.A05.SmoothL2.dir` is exactly this), but it is not
  asserted here and no field below supplies it.

## Out of scope, and asserted nowhere below

Every product estimate of Lemma A.1: `eq:Rproduct`'s first clause
(`:9-13`), `eq:algebra` (`:16`), `eq:tame` (`:17-18`), the componentwise
vector/tensor product forms and the product difference bound of `:50-52`.  The
accepted specification draft `research/A03/Spec.lean` states all of them; only
the clauses below are registered here, and the rest of that draft stays
unregistered.  Also out of scope: `H¹ ↪ L⁶` (`:20`) and `eq:embeddings`
(`:22-26`), which belong to A05 (`verification/Contracts/V1/GradientL6.lean`);
the **torus** half of `lem:calculus` (`:8` "either domain") — everything below
is whole space only; the order shift `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}`; and
derivative-closure of the field classes.

## The class of fields

`SmoothJetsUpTo m` is the hypothesis the clauses below actually run on: smooth,
with the Fréchet jets of order **at most `m`** square integrable.  At `m = 2`
this is the manuscript's `v ∈ H²` for a smooth field
(`paper/sections/02-preliminaries.tex:29-30`, "a classical velocity belongs to
`C([0,S];H^m)` for every integer `m ≥ 0`"), in jet form, and it is exactly what
the proof route uses — only the jets of order `0`, `1` and `2` enter.  It is
weaker than the manuscript's own hypothesis in one respect only: the manuscript
assumes no smoothness and produces a bounded *representative*, whereas a smooth
field is its own representative (see `supNorm_le`).

`SmoothSquareIntegrableJets` is the all-order class — the jet form of
`H^∞` — that lane 019 uses for Lemma B.1
(`verification/Contracts/V1/GradientL6.lean`), kept here so that a consumer
holding it can still apply the clauses: `smoothJetsUpTo_of_allOrders` is that
derived instance.

`Contracts.V1.Data.MemHInfty` (`Contracts/V1/Data.lean:495`) is the *datum* form
of the all-order class: smooth, with an angular Sobolev datum at every integer
order.  `Data.lean:487-491` books the equivalence of the two forms as a separate
lemma (D01 unit L2).  Lane 020 proves the jet ⟹ datum direction; the datum ⟹
jet direction is **open**, is **not** asserted anywhere in this file, and is what
a consumer holding `MemHInfty` still needs in order to reach the fields below.
For the same reason there is deliberately **no** clause with
`Data.sobolevENorm 2 z` on the right: that would require bounding the jet norm
by the datum norm, which is the open direction.  `research/A03/ATTEMPTS.md`
records this in full.

## Conventions

* The right-hand side is `jetSobolevENorm 2`, the sum over orders `j ≤ 2` of the
  `L²` norms of the Fréchet jets, each jet in the operator norm of a
  `j`-multilinear map on `R³`.  The manuscript **defines** its norm on the
  Fourier side: `‖z‖²_{H^s(R³)} = ∫_{R³}(1+|ξ|²)^s|ẑ(ξ)|²dξ`
  (`paper/sections/01-introduction.tex:85-86`) for the angular transform
  `ẑ(ξ) = (2π)^{-3/2}∫e^{-ix·ξ}z(x)dx` of `:91`, with vector and tensor
  components summed in squares (`:103`).  The agreement with
  `jetSobolevENorm 2` is a chain of three links, each costing only factors that
  depend on the dimension `3` and the order `2`:
  1. *Fourier weight ↔ multi-index `ℓ²`.*  The angular transform is an `L²`
     isometry (Plancherel in this normalization, which is why `:91` carries the
     `(2π)^{-3/2}`) and sends `∂^α` to `(iξ)^α` with **no** `2π`, so
     `∫(1+|ξ|²)^2|ẑ|²` is a fixed positive combination of `∑_{|α|≤2}‖∂^αz‖₂²`.
  2. *Multi-index `ℓ²` ↔ jet operator norm.*  For a `j`-multilinear map `T` on
     `R³`, `max_w|T(e_w)| ≤ ‖T‖ ≤ ∑_w|T(e_w)|` over the `3^j` coordinate words
     `w`, and the entries `T(e_w)` of `iteratedFDeriv ℝ j z` are the partial
     derivatives `∂^α z` with `|α| = j`.
  3. *`ℓ²` ↔ `ℓ¹` over the three orders `j ≤ 2`*, a factor of at most `√3`.

  `appendix-a-local-theory.tex:10` allows exactly this: `C` depends only on the
  order and the fixed domain, never on the field or its support.  The field
  `Cinfty` below is therefore *a* constant of `eq:Rproduct`, not its numerical
  value.
* Every norm is `ℝ≥0∞`-valued and none is routed through `.toReal`, so a field
  outside the class cannot make a bound vacuous by an infinite left-hand side.
* No Fourier transform appears in any statement of this file: both sides of
  every clause below are physical-space quantities, so the manuscript's angular
  normalization and Mathlib's cycles normalization cannot differ *in the Lean
  statements*.  The manuscript's own right-hand side is a Fourier quantity, and
  its own proof of this clause is a Fourier argument (`:44-50`); the
  reconciliation is link 1 above, and `research/A03/ATTEMPTS.md` records where
  the `(2π)` factors of the implementation's constant live.

Self-containedness: the only import is another contract, `Contracts.V1.Data`,
from which `SpatialField` and `Space` are reused unchanged.  The three
definitions below name no implementation module; the adapter supplies the `rfl`
bridges.  They live in a nested namespace so that they cannot collide with the
identically-named class of `Contracts.V1.GradientL6`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.BoundedRep

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-- The class the clauses below run on: smooth, with every Fréchet jet of order
at most `m` square integrable.  At `m = 2` this is the manuscript's `v ∈ H²`
for a smooth field, in jet form, and it is exactly the hypothesis
`appendix-a-local-theory.tex:12` needs — the second clause of `eq:Rproduct`
mentions no order above two. -/
def SmoothJetsUpTo (m : ℕ) (v : SpatialField) : Prop :=
  ContDiff ℝ ∞ v ∧ ∀ j ≤ m, MemLp (iteratedFDeriv ℝ j v) 2 volume

/-- The all-order jet form of `02-preliminaries.tex:12` eq:Rinitial's
`H^∞(R³;R³)`: smooth, with every Fréchet jet square integrable.  Field-for-field
the vendor's `EulerLpTranslation.SmoothL2Field`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`), written out here
because a specification may not import an implementation module, and the same
spelling as `Contracts.V1.SmoothSquareIntegrableJets` of the A05 contract.

It is **stronger** than `SmoothJetsUpTo m` and is not the hypothesis of any
clause below; it is kept, together with `smoothJetsUpTo_of_allOrders`, so that a
consumer already holding the A05-style class can apply those clauses unchanged.

This is **not** definitionally `Data.MemHInfty`, which is the datum form; see the
module docstring. -/
def SmoothSquareIntegrableJets (v : SpatialField) : Prop :=
  ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume

/-- `01-introduction.tex:85-86`, `‖v‖_{H^m(R³)}` in jet form: the sum over orders
`j ≤ m` of the `L²` norms of the Fréchet jets of `v`.  See the module docstring
for the three-link comparison with the manuscript's Fourier-side definition.

`ℝ≥0∞`-valued and never routed through `.toReal`: a field with a
non-square-integrable jet of order at most `m` gets `⊤`, so the bounds below are
not satisfiable by an infinite right-hand side being ignored. -/
def jetSobolevENorm (m : ℕ) (v : SpatialField) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (m + 1), eLpNorm (iteratedFDeriv ℝ j v) 2 volume

/-- The bounded-representative clause of Lemma A.1
(`lem:calculus`, `paper/sections/appendix-a-local-theory.tex:12`,
second half of `eq:Rproduct`) on `R³`, in the two forms Section 4 consumes.

The constant is a structure field and is therefore quantified **outside** every
field, every viscosity and every solution, as `appendix-a-local-theory.tex:10`
requires: `C` depends only on the order and the fixed domain, not on the field
or its support. -/
structure BoundedRepresentativeAPI where
  /-- `appendix-a-local-theory.tex:12`, the constant `C` of `‖v‖_∞ ≤ C‖v‖_{H²}`.
  It carries no order index because the order is fixed at two;
  `04-whole-space.tex:53` uses exactly this constant. -/
  Cinfty : ℝ
  /-- `appendix-a-local-theory.tex:10` "`≤ C_m(...)`"; positivity is what makes
  the clauses below nontrivial bounds rather than vanishing ones. -/
  Cinfty_pos : 0 < Cinfty
  /-- The all-order jet class is admissible at every order: a consumer holding
  the A05-style `SmoothSquareIntegrableJets` (lane 019's class, and the jet form
  of `02-preliminaries.tex:12`'s `H^∞`) can apply the two clauses below without
  re-deriving anything.  This is a derived instance, not a second hypothesis:
  the clauses themselves are stated at the weaker `SmoothJetsUpTo`. -/
  smoothJetsUpTo_of_allOrders :
    ∀ (m : ℕ) (v : SpatialField), SmoothSquareIntegrableJets v → SmoothJetsUpTo m v
  /-- `appendix-a-local-theory.tex:12` eq:Rproduct, second clause, in the
  **everywhere-pointwise** form: `‖z(x)‖ ≤ C‖z‖_{H²}` at every point of `R³`.

  This is the manuscript's "bounded representative" with the representative
  already discharged.  `Data.IsSobolevDatum` sees a field only through Schwartz
  pairings and so cannot see a modification on a null set, which is why the
  clause is in general only about a representative
  (`research/A03/Spec.lean`'s `boundedRepresentative`); a field of
  `SmoothJetsUpTo 2` is continuous, hence *is* its own continuous
  representative, and the bound then holds at every point.  It is strictly
  stronger than `eLpNormTop_le`, and it is the form the uniqueness coefficient
  `‖∇u₂‖_∞` of `:120-123` is read through. -/
  supNorm_le :
    ∀ z : SpatialField, SmoothJetsUpTo 2 z →
      ∀ x : Space, ‖z x‖ₑ ≤ ENNReal.ofReal Cinfty * jetSobolevENorm 2 z
  /-- `appendix-a-local-theory.tex:12` eq:Rproduct, second clause, as an
  essential-supremum bound: `‖z‖_{L^∞(R³)} ≤ C‖z‖_{H²}`.

  **This is the field the `A03 → R42` edge carries.**
  `research/section4/STATEMENTS.md:261-262` pins `⟪D01:normLinfty⟫` to the
  ess-sup and `:348-350` states Theorem 4.2's blowup as
  `limsupLeft T (normLinfty ∘ uPert) = ⊤`, so this clause — not the pointwise
  one above — is the literal match for the `04-whole-space.tex:53` step, and it
  is the form in which a bound on `‖·‖_∞` composes with the `L^p` machinery of
  `Contracts/V1/Data.lean`. -/
  eLpNormTop_le :
    ∀ z : SpatialField, SmoothJetsUpTo 2 z →
      eLpNorm z ⊤ volume ≤ ENNReal.ofReal Cinfty * jetSobolevENorm 2 z

end BlowupDensity.Contracts.V1.BoundedRep
