# A01 unit m4 — attempts log (`Section4/A01/PressureGauge.lean`, lane 106)

Goal: the contract field `ManuscriptLocalRegularity.pressure_potential`
(`research/A01/Spec.lean:227-229`) — for every `ClassicalSolutionR ν a f T`,
`PressureGaugeEquivOn (Ico 0 T) (pressurePotential (fun z => pressureGradient u.pressure z.1 z.2)) u.pressure`.

## Route that worked

1. `pressureGradient_fderiv_slice p t x v : fderiv ℝ (p(t,·)) x v = ⟪pressureGradient p t x, v⟫`
   — `pressureGradient` is the Riesz vector of the slice derivative, by basis
   expansion of `v` and `EuclideanSpace.inner_single_left`. From it,
   `pressureGradient_apply` (component form) and `fderiv_eq_of_pressureGradient_eq`
   (equal gradients ⇒ equal slice `fderiv`, by `ContinuousLinearMap.ext`) fall out in 3–4 lines each.
2. Hessian symmetry `hasSymmetricJacobian_pressureGradient`: the new step. Two private helpers:
   - `fderiv_apply_component` — `(fderiv ℝ G x v) b = fderiv ℝ (fun y => (G y) b) x v`
     (coordinate evaluation is the CLM `innerSL ℝ (coordinateVector b)`).
   - `fderiv_fderiv_apply` — `fderiv ℝ (fun y => (fderiv ℝ f y) w) x v = (fderiv ℝ (fderiv ℝ f) x v) w`
     (evaluation-at-`w` is `ContinuousLinearMap.apply ℝ ℝ w`).
   Chaining them with `pressureGradient_apply` turns the goal
   `∂_i(∇p)_j = ∂_j(∇p)_i` into `(D²f (cv i)) (cv j) = (D²f (cv j)) (cv i)`, closed by
   `(ContDiffAt.isSymmSndFDerivAt ...).eq (cv i) (cv j)` — mirroring `D01/DivergenceTime.lean`.
   `contDiff_gradSlice` (smoothness of the gradient slice) reuses `D01.contDiff_slice_scalar`
   + `ContDiff.sum`/`fderiv_right`/`clm_apply` (lane-101 reviewer's 14-line lemma).
3. Gauge wrapping `pressure_potential_of_pointwise` — lane-101 reviewer's `gauge.lean`
   verbatim (`c t := p(t,0) − Q(t,0)`, `is_const_of_fderiv_eq_zero` on `p − Q`), then
   `pressure_potential_of_classicalSolution` discharges its three hypotheses from
   `u.pressure_smooth` via steps 2.

## Failed approaches

- **`rw [hfun, (L.hasFDerivAt.comp x hG.hasFDerivAt).fderiv]` with `hfun : (fun y => (G y) b) = fun y => L (G y)`.**
  `HasFDerivAt.comp` yields the composed function in `Function.comp` form `⇑L ∘ G`, so
  `.fderiv : fderiv ℝ (⇑L ∘ G) x = L.comp (fderiv ℝ G x)`. The rewrite pattern
  `fderiv ℝ (⇑L ∘ G) x` did not match the goal's `fderiv ℝ (fun y => L (G y)) x`
  (rewrite: "Did not find an occurrence of the pattern"). Fixed by stating the function
  equality directly in composition form, `heq : H = ⇑L ∘ G` (proved with
  `funext; simp only [..., Function.comp_apply]`), and `rw [heq]` before `.fderiv`.
  Same fix applied to both `fderiv_apply_component` and `fderiv_fderiv_apply`.

- **The lane-101 reviewer's scratch `slice.lean::hasSymmetricJacobian_gradSlice`** left its
  `hcomp` as a placeholder and closed with `exact (hsymm (cv i) (cv j)).symm`. That `.symm`
  would not have closed the goal: `hcomp`'s RHS was written in the `fderiv ℝ (fun y => fderiv f y w) x v`
  form, which is only *provably* (not defeq) equal to the second-derivative form
  `(fderiv ℝ (fderiv ℝ f) x v) w` — the missing `fderiv_fderiv_apply` reduction. With that
  reduction supplied, the orientation is `(D²f (cv i))(cv j) = (D²f (cv j))(cv i)`, i.e.
  `hsymm.eq (cv i) (cv j)` directly, **no `.symm`**.

- Note on hypotheses: `ContDiff.fderiv_right (m := ∞)` and `ContDiff.differentiable` /
  `ContDiffAt.isSymmSndFDerivAt` all take a side goal `∞ + 1 ≤ ∞` / `1 ≤ ∞` /
  `minSmoothness ℝ 2 ≤ ∞`; `(by simp)` discharges each (matching `RadialPotential.lean`).
  `le_rfl` was avoided since `∞ + 1` is not syntactically `∞`.
