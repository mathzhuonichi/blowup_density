import Contracts.V1.Data

/-! Stable specification for the gradient-`L⁶` clause of Lemma B.1.

Task `collaboration/tasks/A05.md`, graph node `A05`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:195-201`).  Version 1 fixes
**one** clause of Lemma B.1, "Critical embeddings on the two domains"
(`lem:critical-embeddings`, `paper/sections/appendix-b-embeddings.tex:11-38`):
the third line of `eq:critical-derived`,

  `‖∇v‖₆ ≤ C‖Δv‖₂`   (`paper/sections/appendix-b-embeddings.tex:32`),

in the Euclidean case and in the form Proposition 4.3 consumes it
(`paper/sections/04-whole-space.tex:110-112`, reused verbatim by Proposition 4.4
at `:171`).

**Out of scope**, and asserted nowhere below: `eq:critical-embedding-pair`
itself (`appendix-b-embeddings.tex:14-15`), the first two lines of
`eq:critical-derived` (`‖v‖₃ ≤ C‖v‖_{Ḣ^{1/2}}` and
`‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖_{Ḣ^{3/2}}`, `:29-31`), every torus statement, and every
`Ḣ^{1/2}`, `Ḣ^{3/2}`, `Λ` or `J` quantity.  The remaining clauses of the
accepted A05 specification draft (`research/A05/Spec.lean`) stay unregistered;
their proof route is Fourier analysis and is units U1-U8, U10 of
`research/A05/COMPARISON.md:200-215`, whereas this clause is unit U9 and is
**Fourier-free**.

## The class of fields

The manuscript states the derived estimates "whenever the indicated homogeneous
norms are finite" and adds that "in particular they apply to all the smooth
`H^∞` fields used in the article" (`appendix-b-embeddings.tex:26-27,34-37`).
`SmoothSquareIntegrableJets` below is the **jet form** of that smooth `H^∞`
class: smooth, with every Fréchet jet square integrable.  It is the hypothesis
under which the clause is proved here, and it is the weakest one this proof
route uses (only jets of order one, two and three actually enter).

`Contracts.V1.Data.MemHInfty` (`Contracts/V1/Data.lean:495`) is the *datum* form
of the same class: smooth, with an angular Sobolev datum at every integer order.
`Data.lean:487-491` books the equivalence of the two forms as a separate lemma
(unit L2), and that lemma is **not** proved and **not** asserted anywhere in
this file.  A consumer that holds `MemHInfty v` therefore still needs unit L2 to
reach `gradientLSix`.  This is recorded in `research/A05/ATTEMPTS.md`.

## Conventions

* `gradientTensor` is `Data.spatialGradient` (`Contracts/V1/Data.lean:453`) on
  the time-independent lift, so its pointwise norm is the Frobenius quantity
  `(∑_{i,j}|∂_iv_j|²)^{1/2}` of `paper/sections/01-introduction.tex:103`, not an
  operator norm.
* `laplacian` is the pinned upstream componentwise Euclidean Laplacian
  `∑ᵢ∂ᵢ∂ᵢu` (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:76`)
  on the same lift, which is the `Δu` of `eq:RH1`.
* Every norm is `ℝ≥0∞`-valued and none is routed through `.toReal`, so the bound
  is never satisfiable by an infinite left-hand side.
* No Fourier transform appears in any statement of this file, so the manuscript's
  angular normalization and Mathlib's cycles normalization cannot differ here:
  `‖·‖₂`, `‖∇·‖₆` and `‖Δ·‖₂` are all physical-space quantities
  (`research/A05/COMPARISON.md:126-128`).

Self-containedness: the only import is another contract, `Contracts.V1.Data`,
from which `SpatialField`, `spatialGradient`, `spatialDerivative`,
`spatialLaplacian` and `coordinateVector` are reused unchanged.  Nothing here
names an implementation module; the adapter supplies the `rfl` bridges.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-- The time-independent lift of a spatial field, so that the pinned upstream
spacetime operators can be reused verbatim on a fixed-time slice.  Same device as
`Data.IsSolenoidal` (`Contracts/V1/Data.lean:504`) and as `research/A05/Spec.lean`. -/
def lift (v : SpatialField) : SpaceTimeField := fun z => v z.2

/-- `appendix-b-embeddings.tex:97` "Apply the `a = 1/2` inequality to each
`∂_jv`": the `j`-th coordinate derivative of a spatial field, as a spatial field.
It is the `j`-th column of `gradientTensor`. -/
def partialDeriv (j : Fin 3) (v : SpatialField) : SpatialField :=
  fun x => spatialDerivative (lift v) 0 x (coordinateVector j)

/-- `04-whole-space.tex:112`, the tensor `∇v`.  This is `Data.spatialGradient`
(`Contracts/V1/Data.lean:453`) on the time-independent lift, hence the Frobenius
assembly of `01-introduction.tex:103`. -/
def gradientTensor (v : SpatialField) : Space → WithLp 2 (Fin 3 → Space) :=
  fun x => spatialGradient (lift v) 0 x

/-- `04-whole-space.tex:110-112`, the field `Δv` of `eq:RH1`: the pinned upstream
componentwise Euclidean Laplacian on the time-independent lift. -/
def laplacian (v : SpatialField) : SpatialField :=
  fun x => spatialLaplacian (lift v) 0 x

/-- The jet form of `02-preliminaries.tex:12` eq:Rinitial's `H^∞(R³;R³)`, i.e.
of the "smooth `H^∞` fields" of `appendix-b-embeddings.tex:36-37`: smooth, with
every Fréchet jet square integrable.  Field-for-field the vendor's
`EulerLpTranslation.SmoothL2Field`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`), written out here
because a specification may not import an implementation module.

This is **not** definitionally `Data.MemHInfty`, which is the datum form; see the
module docstring. -/
def SmoothSquareIntegrableJets (v : SpatialField) : Prop :=
  ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume

/-- Lemma B.1's gradient-`L⁶` clause (`appendix-b-embeddings.tex:32`,
`eq:critical-derived` third line) together with the identity
`04-whole-space.tex:112` names as its ingredient.

The constant is a structure field and is therefore quantified **outside** every
field, every viscosity and every solution, as
`appendix-b-embeddings.tex:109-110` requires: "All constants depend only on the
fixed exponents, domain, and norm conventions, not on the field or its frequency
support." -/
structure GradientL6API where
  /-- `appendix-b-embeddings.tex:32` and `04-whole-space.tex:112`: the universal
  constant of `‖∇v‖₆ ≤ C‖Δv‖₂`. -/
  Csix : ℝ
  /-- `appendix-b-embeddings.tex:12-13` "there are finite constants"; positivity
  is what makes the clause a nontrivial bound rather than a vanishing one. -/
  Csix_pos : 0 < Csix
  /-- `04-whole-space.tex:112` "since Plancherel gives `‖D²u‖₂ = ‖Δu‖₂`": the
  squared Frobenius `L²` norm of the Hessian equals that of the Laplacian.  This
  is the manuscript's stated ingredient for the clause below, so it is recorded
  rather than left implicit.  Both sides are ordinary Bochner integrals of
  nonnegative functions, finite on this class. -/
  hessianLaplacianIdentity :
    ∀ v : SpatialField, SmoothSquareIntegrableJets v →
      ∑ i : Fin 3, ∑ j : Fin 3, (∫ x, ‖partialDeriv i (partialDeriv j v) x‖ ^ 2)
        = ∫ x, ‖laplacian v x‖ ^ 2
  /-- `appendix-b-embeddings.tex:32` eq:critical-derived, third line, as
  `04-whole-space.tex:110-112` consumes it: `‖∇v‖₆ ≤ C‖Δv‖₂`, with the Frobenius
  `L⁶` norm of the gradient tensor on the left and the `L²` norm of the
  componentwise Laplacian on the right, in `ℝ≥0∞`. -/
  gradientLSix :
    ∀ v : SpatialField, SmoothSquareIntegrableJets v →
      eLpNorm (gradientTensor v) 6 volume
        ≤ ENNReal.ofReal Csix * eLpNorm (laplacian v) 2 volume

end BlowupDensity.Contracts.V1
