import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A03.OuterTameProduct
import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.DatumToJets

/-!
# A04 unit G1, sub-lemma SL5 row 5a: the advection term in divergence form

Task `A04` (graph node `formalization/blueprint/DEPENDENCY_GRAPH.md`), the
force-density energy estimate `eq:Rhigh` (`paper/sections/04-whole-space.tex`).
Row 5a of the SL5 split (`research/A04/SL5_SPLIT.md`) supplies the shape row 5c
consumes: the nonlinear datum `N = ∑ⱼ derivDatumStep m j (castOrder … Bⱼ)` needs
the advection slice written as the divergence of the column tensor,

`(u·∇)u(t,·) = ∑ⱼ ∂ⱼ(u_j·u)`  as functions of `x`,

with `z := fun x => u(t,x)`.

## What is proved

* `convectionDivergence_eq_sum_partialDeriv_outerColumn`: the definitional bridge
  `∇·(u⊗u)(t,x) = ∑ⱼ partialDeriv j (outerColumn z z j) x` — both sides are the
  same sum of `fderiv`s of `x ↦ (u(t,x) j) • u(t,x)` in the `j`-th coordinate
  direction, so it is `rfl`.  This turns lane 093's tensor divergence
  (`Section4/A01/ConvectionDivergence.lean`) into A03's `partialDeriv`/`outerColumn`
  spelling without re-deriving the Leibniz rule.
* `advection_eq_sum_partialDeriv_outerColumn`: SL5 row 5a proper.  Composing the
  bridge with lane 093's divergence-free specialization
  `convectionDivergence_eq_advection` gives, on a divergence-free field, the
  advection slice as a **function of `x`** in divergence form.
* `advection_slice_eq_sum_partialDeriv_outerColumn`: the `ClassicalSolutionR`
  corollary, discharging the two hypotheses from `velocity_smooth` (via
  `D01.contDiff_slice`, the slice-smoothness pattern) and the `divergence` field.

## Reuse

Nothing here restates a definition.  `convectionDivergence` and
`convectionDivergence_eq_advection` are lane 093's
(`Section4/A01/ConvectionDivergence.lean:60,113`); `partialDeriv`, `outerColumn`
are `Section4/A03/OuterTameProduct.lean:59,68`; `advection`, `spatialDivergence`
are the upstream `NavierStokes.ProblemStatement` (`vendor/.../ProblemStatement.lean:63,67`);
`contDiff_slice`, `ClassicalSolutionR` are D01/A02's.
-/

noncomputable section

open Set
open NavierStokes.ProblemStatement

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A01 (convectionDivergence convectionDivergence_eq_advection)
open NSFormalization.Section4.A03 (partialDeriv outerColumn)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NSFormalization.Section4.D01 (contDiff_slice)
open scoped ContDiff

/-- **The definitional bridge (SL5 row 5a, step i).**  The tensor divergence
`∇·(u⊗u)` of lane 093 is, column by column, the `j`-th partial derivative of the
`j`-th column `outerColumn z z j = u_j·u` of `u⊗u` (`z := u(t,·)`): both sides are
`∑ⱼ fderiv ℝ (fun y => (u(t,y) j) • u(t,y)) x eⱼ`.  Holds unconditionally; it is
`rfl` because `partialDeriv`/`outerColumn`/`lift`/`spatialDerivative` unfold to the
same `fderiv` sum as `convectionDivergence`. -/
theorem convectionDivergence_eq_sum_partialDeriv_outerColumn
    (u : SpaceTimeField) (t : ℝ) (x : Space) :
    convectionDivergence u t x
      = ∑ j : Fin 3,
          partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) x := rfl

/-- **SL5 row 5a.**  On a field differentiable in space and divergence free at
every point of the slice `t`, the advection `(u·∇)u(t,·)` equals the divergence
form `∑ⱼ ∂ⱼ(u_j·u)`, stated as an identity of functions of `x` so row 5c can
rewrite it under `IsSobolevDatum`.  The proof composes the definitional bridge
with lane 093's divergence-free specialization
`convectionDivergence_eq_advection`; no new analysis. -/
theorem advection_eq_sum_partialDeriv_outerColumn {u : SpaceTimeField} {t : ℝ}
    (hdiff : ∀ x, DifferentiableAt ℝ (fun y => u (t, y)) x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    (fun x => advection u t x)
      = fun x => ∑ j : Fin 3,
          partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) x := by
  funext x
  rw [← convectionDivergence_eq_advection u t x (hdiff x) (hdiv x)]
  exact convectionDivergence_eq_sum_partialDeriv_outerColumn u t x

/-- **SL5 row 5a, the `ClassicalSolutionR` corollary.**  For a classical whole-space
solution `w` and a time `t ∈ [0,T)`, the velocity's advection slice is in
divergence form.  Space-differentiability of the slice comes from `velocity_smooth`
through `D01.contDiff_slice` (the slice-smoothness pattern), and the divergence
vanishing is the `divergence` field. -/
theorem advection_slice_eq_sum_partialDeriv_outerColumn
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    (fun x => advection w.velocity t x)
      = fun x => ∑ j : Fin 3,
          partialDeriv j
            (outerColumn (fun y => w.velocity (t, y)) (fun y => w.velocity (t, y)) j) x := by
  have hcd : ContDiff ℝ ∞ (fun y : Space => w.velocity (t, y)) :=
    contDiff_slice w.velocity_smooth ht
  exact advection_eq_sum_partialDeriv_outerColumn
    (fun x => (hcd.differentiable (by simp)).differentiableAt)
    (w.divergence t ht)

end NSFormalization.Section4.A04
