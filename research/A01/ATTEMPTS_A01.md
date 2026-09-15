# A01 — attempts log (lane 093, unit E1)

Non-generated record of failed approaches while proving unit **E1**
(`formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean`).

## Target

`convectionDivergence u t x = advection u t x + (spatialDivergence u t x) • u(t,x)`
for `u` differentiable in space at `(t,x)`, where
`convectionDivergence u t x = ∑_j fderiv ℝ (fun y => u(t,y) j • u(t,y)) x (eⱼ)`.
Per-`j` Leibniz product rule, then two `Finset` sum manipulations (a basis
expansion for the advection sum, `Finset.sum_smul` for the divergence sum).

## Failed / corrected approaches (each a compile iteration)

1. **`HasFDerivAt.comp` without the explicit point `x`.**
   `(EuclideanSpace.proj j).hasFDerivAt.comp hu.hasFDerivAt` →
   *"argument DifferentiableAt.hasFDerivAt hu has type Prop but expected Type"*.
   Cause: in `Mathlib/Analysis/Calculus/FDeriv/Comp.lean` the `section
   Composition` has `variable (x)` **explicit**, so `HasFDerivAt.comp` is
   `comp (x) (hg) (hf)`; the point must be passed.  Fix: `… .comp x hu.hasFDerivAt`.

2. **Ascribing `hc`'s function as `fun y => u(t,y) j`.**  Higher-order
   unification failure: the expected `⇑?g ∘ (fun y => u(t,y))` cannot be solved
   against `fun y => (u(t,y)).ofLp j` (Lean cannot invert to `?g = proj j`), so
   `?g` stayed a metavariable and the term collapsed to a `HasFDerivAtFilter`.
   Fix: do **not** ascribe `hc`'s function; ascribe only `hprod`'s function and
   derivative (first-order defeq, no HOU), letting `⇑L ∘ g` be `hc`'s natural
   shape.

3. **`hc.smul` / dot notation resolving to `HasFDerivAtFilter.smul`.**
   `hc : HasFDerivAt …` but `.smul` dot notation unfolded `HasFDerivAt` to
   `HasFDerivAtFilter` and searched `HasFDerivAtFilter.smul` (nonexistent).
   Correcting to explicit `HasFDerivAt.smul hc …` then gave *"unknown constant
   `HasFDerivAt.smul`"* — the lemma lives in `Mathlib/Analysis/Calculus/FDeriv/
   Mul.lean`, which was **not** in the transitive import closure of
   `NavierStokes.R3.ProblemStatement`.  Fix: `import
   Mathlib.Analysis.Calculus.FDeriv.Mul` (then `hc.smul` resolves).

4. **`(EuclideanSpace.proj j).hasFDerivAt` with `𝕜`/`StrongDual` unresolved.**
   `ContinuousLinearMap.hasFDerivAt` takes `f` **explicit**; and
   `EuclideanSpace.proj j : StrongDual 𝕜 …` left `𝕜` a metavariable, printed as
   `StrongDual ?m (EuclideanSpace ?m (Fin 3))` against the expected CLM type.
   Fix: bind `let L : Space →L[ℝ] ℝ := EuclideanSpace.proj j` (the ascription
   pins `𝕜 = ℝ` and makes `StrongDual ℝ Space` defeq to the CLM type), and pass
   `ContinuousLinearMap.hasFDerivAt L` with `f := L` explicit.

5. **Second sum bullet closed by `rw [← Finset.sum_smul]` alone.**  Left
   `(∑ i, (∂ᵢu)ᵢ) • u = spatialDivergence • u`; `rw`'s terminal reducible-rfl did
   not unfold the semireducible `spatialDivergence`.  Fix: append a `rfl`
   (default-transparency defeq unfolds `spatialDivergence`, `spatialDerivative`,
   and `EuclideanSpace.proj`/`.ofLp`).

## What worked (the shape that compiles)

* Component derivative via a `let`-bound `L := EuclideanSpace.proj j`, then
  `HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt L) hu.hasFDerivAt`.
* `HasFDerivAt.smul` with `hprod`'s function ascribed to
  `fun y => u(t,y) j • u(t,y)` (defeq to `⇑L ∘ g • g`), so `rw [hprod.fderiv]`
  matches `convectionDivergence`'s summand syntactically.
* Advection sum: mirror `A03/OuterTameProduct.lean:279` `advectionOf_eq` —
  `u(t,x) = ∑ⱼ (u(t,x) j) • eⱼ` (`ext k; simp [coordinateVector,
  Pi.single_apply]`), `conv_rhs => rw [hy]`, `map_sum`, then
  `Finset.sum_congr rfl (fun j _ => (map_smul _ _ _).symm)`.
* `navierStokesResidual_eq_iff_projected`: `unfold navierStokesResidual`,
  `rw [convectionDivergence_eq_advection …]`, then
  `constructor <;> intro h <;> · rw [← sub_eq_zero] at h ⊢; rw [← h]; abel`
  (both directions reduce to the same abelian identity).

## Deprecations avoided

`ContinuousLinearMap.add_apply` / `ContinuousLinearMap.smul_apply` are
deprecated in this Mathlib; used the root `add_apply` / `smul_apply` so
`lake env lean` on the module is silent (no warnings).

## Next A01 lane (reviewer recommendation, `research/A01/REVIEW_SPLIT.md` §6)

**Unit P1** — `pressurePotential G` has gradient `G` under `HasSymmetricJacobian G`
(the radial potential `p(x) = ∫₀¹ G(rx)·x dr` of `02-preliminaries.tex:96-100`).
Sized **M**.  It is the only M-sized A01 unit with **no dependency and no gap**:
`COMPARISON.md:191` has both its `depends on` and `blocker` columns empty, the
manuscript hands over the whole proof in two lines
(`∂_j p = ∫₀¹ ∂_r[r G_j(rx)] dr = G_j`), and the only Lean work is
differentiating under `intervalIntegral` with its side conditions + FTC.  It pays
twice: it discharges `ManuscriptLocalRegularity.pressure_potential` (unit m4)
outright **and** it is D01 unit **L9(b)**, retiring an item in two ledgers.
Everything on the true spine (A3, B1, C1b, C1c) is an L-campaign needing a plan
lane first, and P2 is gated on a Liouville statement Mathlib lacks — P1 is the
one shovel-ready unit.

Inputs: `pressurePotential` (`verification/Contracts/V1/Data.lean:596`),
`HasSymmetricJacobian` (`research/A01/Spec.lean:117`, now carrying
`Differentiable ℝ G` per `REVIEW.md` H2), `pressureGradient`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:67`),
`PressureGaugeEquivOn` (`Data.lean:589`), Mathlib differentiation-under-the-
integral + FTC.

The ~20-line free harvest `projected_of_classicalSolution` was folded in already
this lane (`Section4/A01/ProjectedEquation.lean`), so m3 is retired.
