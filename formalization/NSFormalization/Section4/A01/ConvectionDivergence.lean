import NavierStokes.R3.ProblemStatement
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# A01 unit E1: the tensor divergence `∇·(u⊗u)` equals the advection `(u·∇)u`

Task `A01` (graph node `formalization/blueprint/DEPENDENCY_GRAPH.md:172`), the
first bounded sub-lemma of the whole-space local solution adapter.  This is
unit **E1** of `research/A01/COMPARISON.md` §3 and the calculus identity the
reviewer flagged (`research/A01/REVIEW.md` L7) as the bridge that turns
`ClassicalSolutionR.momentum` into the projected forced equation `eq:projected`
(`paper/sections/02-preliminaries.tex:81`,
`paper/sections/appendix-a-local-theory.tex:76-77`).

## The object

`convectionDivergence` is the manuscript's tensor divergence `∇·(u⊗u)`, whose
`k`-th component is `∑_j ∂_j(u_j u_k)`, written literally as the vector-valued
spatial derivative `∑_j ∂_j (u_j • u)` at frozen time.  It is one of the two
objects `research/D01/RECONCILIATION.md:190` records as "genuinely absent" from
`Data.lean`, deliberately left for `prop:local`, its first consumer; it is
introduced token-for-token as in `research/A01/Spec.lean:103-105`.  A01 owns it,
so this module is its first home in `formalization/` (a `grep` of
`formalization/NSFormalization` finds no prior definition).

## What is proved

For a field differentiable in space at `(t,x)`, the Leibniz rule gives
`∇·(u⊗u) = (u·∇)u + (∇·u) u`, so on a divergence-free field the tensor
divergence and the advection coincide.  Concretely:

* `convectionDivergence_eq_advection_add_smul_div`: the general Leibniz identity
  `∇·(u⊗u) = (u·∇)u + (∇·u) • u`;
* `convectionDivergence_eq_advection`: its divergence-free specialization;
* `navierStokesResidual_eq_iff_projected`: the payoff, that the momentum form
  `navierStokesResidual ν u p = F` (which `ClassicalSolutionR.momentum` asserts)
  and the projected form of `research/A01/Spec.lean`'s `projected` field are
  equivalent at any differentiable, divergence-free point.

The advection `(u·∇)u` is the upstream `NavierStokes.ProblemStatement.advection`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:63`); the
divergence is `spatialDivergence` (`:67`); the `ν`-scaled residual is
`NavierStokesR3.ProblemStatement.navierStokesResidual`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:57`).  Nothing
here restates an upstream definition: they are imported.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set
open NavierStokes.ProblemStatement

/-- `paper/sections/02-preliminaries.tex:81` (`eq:projected`) and `:90`
(`eq:Rpressure`): the tensor divergence `∇·(u⊗u)`, whose `k`-th component is
`∑_j ∂_j(u_j u_k)`.  Written literally as `∑_j ∂_j (u_j • u)`, a vector-valued
spatial derivative at frozen time; the same spelling as
`research/A01/Spec.lean:103-105`. -/
def convectionDivergence (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  ∑ j : Fin 3,
    fderiv ℝ (fun y : Space => (u (t, y) j) • u (t, y)) x (coordinateVector j)

/-- The `j`-th Leibniz term: differentiating the product `u_j • u` in the
`j`-direction splits into `(∂_j u_j) • u + u_j • (∂_j u)` written with the
components pulled out. -/
private theorem convection_term
    (u : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) (j : Fin 3) :
    fderiv ℝ (fun y : Space => (u (t, y) j) • u (t, y)) x (coordinateVector j)
      = (u (t, x) j) • fderiv ℝ (fun y : Space => u (t, y)) x (coordinateVector j)
        + (fderiv ℝ (fun y : Space => u (t, y)) x (coordinateVector j) j)
            • u (t, x) := by
  let L : Space →L[ℝ] ℝ := EuclideanSpace.proj j
  have hprojd : HasFDerivAt (⇑L) L (u (t, x)) := ContinuousLinearMap.hasFDerivAt L
  have hc : HasFDerivAt (⇑L ∘ fun y : Space => u (t, y))
      (L.comp (fderiv ℝ (fun y : Space => u (t, y)) x)) x :=
    HasFDerivAt.comp x hprojd hu.hasFDerivAt
  have hprod : HasFDerivAt (fun y : Space => u (t, y) j • u (t, y))
      (u (t, x) j • fderiv ℝ (fun y : Space => u (t, y)) x
        + (L.comp (fderiv ℝ (fun y : Space => u (t, y)) x)).smulRight (u (t, x))) x :=
    HasFDerivAt.smul hc hu.hasFDerivAt
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply]
  rfl

/-- **Leibniz rule for the tensor divergence.**  For a field differentiable in
space at `(t,x)`,
`∇·(u⊗u) = (u·∇)u + (∇·u) • u`.  (`appendix-a-local-theory.tex:76-77`, the
identity behind eq:projected.) -/
theorem convectionDivergence_eq_advection_add_smul_div
    (u : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x) :
    convectionDivergence u t x
      = advection u t x + (spatialDivergence u t x) • u (t, x) := by
  rw [convectionDivergence, Finset.sum_congr rfl (fun j _ => convection_term u t x hu j),
    Finset.sum_add_distrib]
  congr 1
  · -- `∑_j (u_j) • ∂_j u = (u·∇)u`, by expanding `u(t,x)` in the coordinate basis
    have hy : u (t, x) = ∑ j : Fin 3, (u (t, x) j) • coordinateVector j := by
      ext k; simp [coordinateVector, Pi.single_apply]
    show _ = fderiv ℝ (fun y : Space => u (t, y)) x (u (t, x))
    conv_rhs => rw [hy]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (map_smul _ _ _).symm
  · -- `∑_j (∂_j u)_j • u = (∇·u) • u`
    rw [← Finset.sum_smul]
    rfl

/-- **Divergence-free specialization.**  On a divergence-free field the tensor
divergence is the advection, `∇·(u⊗u) = (u·∇)u`.  (Unit E1.) -/
theorem convectionDivergence_eq_advection
    (u : VelocityField) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (hdiv : spatialDivergence u t x = 0) :
    convectionDivergence u t x = advection u t x := by
  rw [convectionDivergence_eq_advection_add_smul_div u t x hu, hdiv, zero_smul, add_zero]

/-- **The E1 payoff.**  At a point where the velocity is differentiable in space
and divergence free, the momentum form of the equation
(`NavierStokesR3.ProblemStatement.navierStokesResidual ν u p = F`, which
`ClassicalSolutionR.momentum` asserts, `Section4/A02/SolutionClass.lean:130`) is
equivalent to the projected forced form of `research/A01/Spec.lean`'s `projected`
field.  This is the calculus content that lets a `ClassicalSolutionR` discharge
`ManuscriptLocalRegularity.projected`. -/
theorem navierStokesResidual_eq_iff_projected
    (ν : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) (F : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (hdiv : spatialDivergence u t x = 0) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = F
      ↔ temporalDerivative u t x - ν • spatialLaplacian u t x
          = (F - convectionDivergence u t x) - pressureGradient p t x := by
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual
  rw [convectionDivergence_eq_advection u t x hu hdiv]
  constructor <;> intro h <;>
    · rw [← sub_eq_zero] at h ⊢
      rw [← h]; abel

end NSFormalization.Section4.A01
