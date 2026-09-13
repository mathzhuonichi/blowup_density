import NSFormalization.Section4.A01.RadialPotential
import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.DatumToJets
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A01 · unit m4: the pressure is the radial potential of its own gradient, up to a gauge

`paper/sections/02-preliminaries.tex:96-100`, `research/A01/Spec.lean:225-229`.

This module discharges the contract field
`ManuscriptLocalRegularity.pressure_potential`: for every classical whole-space
solution `u`, the pressure `u.pressure` is gauge-equivalent on `Ico 0 T` to the
manuscript's explicit radial potential of its own spatial gradient,
`PressureGaugeEquivOn (Ico 0 T) (pressurePotential (fun z => pressureGradient u.pressure z.1 z.2)) u.pressure`.

## What is proved

* `pressureGradient_fderiv_slice` — `pressureGradient p t x` is the Riesz vector
  of the spatial slice derivative: `∂_v (p(t,·)) x = ⟪pressureGradient p t x, v⟫`.
* `fderiv_eq_of_pressureGradient_eq` — equal gradients ⇒ equal slice derivatives.
* `hasSymmetricJacobian_pressureGradient` and `contDiff_gradSlice` — the spatial
  gradient of a slice of a `ContDiffOn ℝ ∞` pressure has a symmetric Jacobian
  (Clairaut / symmetry of the second Fréchet derivative,
  `ContDiffAt.isSymmSndFDerivAt`) and is itself `ContDiff ℝ ∞`.
* `pressure_potential_of_pointwise` — the gauge wrapping: at each interior time
  the pressure and its own radial potential have the same spatial gradient
  (lane 101's `pressureGradient_pressurePotential`), so their difference has zero
  spatial derivative and is constant in space (`is_const_of_fderiv_eq_zero`).
* `pressure_potential_of_classicalSolution` — the contract field, specialised to
  `ClassicalSolutionR`.

## Reuse

* `pressurePotential`, `HasSymmetricJacobian`, `hasFDerivAt_radialPotential`,
  `pressureGradient_pressurePotential` — `Section4/A01/RadialPotential.lean` (lane 101, PR #103).
* `PressureGaugeEquivOn`, `ClassicalSolutionR` — `Section4/A02/SolutionClass.lean:109,114`.
* `contDiff_slice_scalar` — `Section4/D01/DatumToJets.lean:377`.
* `pressureGradient`, `coordinateVector`, `Space` — `NavierStokes.ProblemStatement`.
* The gauge wrapping and helper skeleton follow the lane-101 reviewer's scratch
  `/tmp/a01p1rev/{gauge.lean,slice.lean}`; the Hessian-symmetry step (the gap the
  scratch left open in `hasSymmetricJacobian_gradSlice.hcomp`) is completed here via
  the two component/second-derivative lemmas below, mirroring
  `Section4/D01/DivergenceTime.lean`'s use of `isSymmSndFDerivAt`.
-/

noncomputable section
namespace NSFormalization.Section4.A01.PressureGauge

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A02 (PressureGaugeEquivOn ClassicalSolutionR)
open scoped ContDiff RealInnerProductSpace

/-! ## 1. `pressureGradient` is the Riesz vector of the slice derivative -/

/-- **The gradient identity (m4 helper 1).**  `pressureGradient p t x` is the
Riesz representative of the slice Fréchet derivative `∂(p(t,·))(x)`: for every
direction `v`, `fderiv ℝ (p(t,·)) x v = ⟪pressureGradient p t x, v⟫`. -/
theorem pressureGradient_fderiv_slice (p : PressureField) (t : ℝ) (x v : Space) :
    fderiv ℝ (fun y : Space => p (t, y)) x v = (inner ℝ (pressureGradient p t x) v : ℝ) := by
  have basisL : ∀ (u : Space) (j : Fin 3), (inner ℝ (coordinateVector j) u : ℝ) = u j := by
    intro u j; rw [coordinateVector, EuclideanSpace.inner_single_left]; simp
  have expand : ∀ (u : Space),
      u = u 0 • coordinateVector 0 + u 1 • coordinateVector 1 + u 2 • coordinateVector 2 := by
    intro u; ext i; fin_cases i <;> simp [coordinateVector]
  simp only [pressureGradient, Fin.sum_univ_three, inner_add_left, real_inner_smul_left, basisL]
  conv_lhs => rw [expand v]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

/-- Two pressures whose spatial gradients agree at time `t` have equal slice
Fréchet derivatives there. -/
theorem fderiv_eq_of_pressureGradient_eq {p q : PressureField} {t : ℝ}
    (h : ∀ x : Space, pressureGradient p t x = pressureGradient q t x) (x : Space) :
    fderiv ℝ (fun y : Space => p (t, y)) x = fderiv ℝ (fun y : Space => q (t, y)) x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [pressureGradient_fderiv_slice p t x v, pressureGradient_fderiv_slice q t x v, h x]

/-- Reading off a single directional component of the gradient. -/
theorem pressureGradient_apply (p : PressureField) (t : ℝ) (x : Space) (j : Fin 3) :
    pressureGradient p t x j = fderiv ℝ (fun y : Space => p (t, y)) x (coordinateVector j) := by
  rw [pressureGradient_fderiv_slice p t x (coordinateVector j), coordinateVector,
    EuclideanSpace.inner_single_right]
  simp

/-! ## 2. The Hessian is symmetric, so `∇(p(t,·))` has a symmetric Jacobian -/

/-- Component of a Fréchet derivative through coordinate evaluation: the `b`-th
coordinate of `fderiv ℝ G x v` is the derivative of the scalar component
`fun y => (G y) b`.  Evaluation `EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ` is the
continuous linear map `innerSL ℝ (coordinateVector b)`. -/
private theorem fderiv_apply_component {G : Space → Space} {x : Space}
    (hG : DifferentiableAt ℝ G x) (v : Space) (b : Fin 3)
    {H : Space → ℝ} (hH : H = fun y : Space => (G y) b) :
    (fderiv ℝ G x v) b = fderiv ℝ H x v := by
  have hpt : ∀ u : Space, (u b : ℝ) = (innerSL ℝ (coordinateVector b)) u := by
    intro u
    rw [innerSL_apply_apply, coordinateVector, EuclideanSpace.inner_single_left]
    simp
  have heq : H = ⇑(innerSL ℝ (coordinateVector b)) ∘ G := by
    funext y
    simp only [hH, Function.comp_apply]
    exact hpt (G y)
  rw [heq, ((innerSL ℝ (coordinateVector b)).hasFDerivAt.comp x hG.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply]
  exact hpt (fderiv ℝ G x v)

/-- Interchange: the derivative of `fun y => (fderiv ℝ f y) w` in direction `v`
is the second derivative `(fderiv ℝ (fderiv ℝ f) x v) w`.  Uses that
`ContinuousLinearMap.apply` acts as evaluation at `w`. -/
private theorem fderiv_fderiv_apply {f : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v w : Space) :
    fderiv ℝ (fun y : Space => (fderiv ℝ f y) w) x v = (fderiv ℝ (fderiv ℝ f) x v) w := by
  have heq : (fun y : Space => (fderiv ℝ f y) w)
      = ⇑(ContinuousLinearMap.apply ℝ ℝ w) ∘ (fderiv ℝ f) := by
    funext y; simp [Function.comp_apply]
  rw [heq, ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp x hf.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-- **`∇(p(t,·))` is `ContDiff ℝ ∞` (m4 helper).**  The spatial gradient of the
smooth pressure slice is smooth.  (Lane-101 reviewer's `contDiff_gradSlice`,
routed through D01's `contDiff_slice_scalar`.) -/
theorem contDiff_gradSlice {T : ℝ} {p : PressureField}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y) := by
  have h := NSFormalization.Section4.D01.contDiff_slice_scalar hp ht
  simp only [pressureGradient]
  exact ContDiff.sum (fun i _ =>
    ((h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).smul contDiff_const)

/-- **The symmetric-Jacobian hypothesis (m4 helper 2, the new step).**  For a
pressure `p` smooth on the closed-at-zero slab and an interior time `t`, the
spatial gradient `x ↦ ∇(p(t,·))(x)` has a symmetric Jacobian
`∂_i(∇p)_j = ∂_j(∇p)_i`.  This is Clairaut's theorem: `(∇p)_j = ∂_j(p(t,·))`, so
`∂_i(∇p)_j = ∂_i∂_j p = ∂_j∂_i p` by symmetry of the second Fréchet derivative
(`ContDiffAt.isSymmSndFDerivAt`, the pattern of `Section4/D01/DivergenceTime.lean`). -/
theorem hasSymmetricJacobian_pressureGradient {T : ℝ} {p : PressureField}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasSymmetricJacobian (fun x : Space => pressureGradient p t x) := by
  have hslice : ContDiff ℝ ∞ (fun z : Space => p (t, z)) :=
    NSFormalization.Section4.D01.contDiff_slice_scalar hp ht
  have hgrad : ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y) := contDiff_gradSlice hp ht
  refine ⟨hgrad.differentiable (by simp), ?_⟩
  intro x i j
  have hGdiff : DifferentiableAt ℝ (fun y : Space => pressureGradient p t y) x :=
    (hgrad.differentiable (by simp)) x
  have hff : DifferentiableAt ℝ (fderiv ℝ (fun z : Space => p (t, z))) x :=
    ((hslice.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hsymm := (hslice.contDiffAt (x := x)).isSymmSndFDerivAt (n := ∞) (by simp)
  have hcomp : ∀ (a b : Fin 3),
      (fderiv ℝ (fun y : Space => pressureGradient p t y) x (coordinateVector a)) b
        = (fderiv ℝ (fderiv ℝ (fun z : Space => p (t, z))) x (coordinateVector a))
            (coordinateVector b) := by
    intro a b
    have hH : (fun y : Space => (fderiv ℝ (fun z : Space => p (t, z)) y) (coordinateVector b))
        = fun y : Space => ((fun y : Space => pressureGradient p t y) y) b :=
      funext (fun y => (pressureGradient_apply p t y b).symm)
    rw [fderiv_apply_component hGdiff (coordinateVector a) b hH,
      fderiv_fderiv_apply hff (coordinateVector a) (coordinateVector b)]
  rw [hcomp i j, hcomp j i]
  exact hsymm.eq (coordinateVector i) (coordinateVector j)

/-! ## 3. The gauge wrapping -/

/-- **The gauge wrapping (m4 core).**  If, at every interior time, `∇p(t,·)` has a
symmetric Jacobian, is smooth, and `p(t,·)` is differentiable, then `p` differs
from the radial potential of its own gradient by a function of time on `Ico 0 T`.
(Lane-101 reviewer's `pressure_potential_of_pointwise`, `/tmp/a01p1rev/gauge.lean`,
verbatim except that `PressureGaugeEquivOn` is now A02's and
`fderiv_eq_of_pressureGradient_eq` is the version above.) -/
theorem pressure_potential_of_pointwise {T : ℝ} (p : PressureField)
    (hsym : ∀ t ∈ Ico (0 : ℝ) T, HasSymmetricJacobian (fun y : Space => pressureGradient p t y))
    (hsm : ∀ t ∈ Ico (0 : ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y))
    (hdp : ∀ t ∈ Ico (0 : ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) :
    PressureGaugeEquivOn (Ico (0 : ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient p z.1 z.2)) p := by
  classical
  set Q : PressureField :=
    pressurePotential (fun z : SpaceTime => pressureGradient p z.1 z.2) with hQ
  refine ⟨fun t => p (t, 0) - Q (t, 0), ?_⟩
  intro t ht x
  have hgrad : ∀ y : Space, pressureGradient Q t y = pressureGradient p t y := by
    intro y
    exact pressureGradient_pressurePotential (hsym t ht) (hsm t ht) (fun _ => rfl) y
  have hQd : Differentiable ℝ (fun y : Space => Q (t, y)) := by
    rw [hQ]
    intro y
    exact (hasFDerivAt_radialPotential (hsym t ht) (hsm t ht) y).differentiableAt
  have hfd : ∀ y : Space, fderiv ℝ (fun y : Space => p (t, y)) y
      = fderiv ℝ (fun y : Space => Q (t, y)) y :=
    fun y => fderiv_eq_of_pressureGradient_eq (fun z => (hgrad z).symm) y
  have hconst : ∀ y : Space, p (t, y) - Q (t, y) = p (t, 0) - Q (t, 0) := by
    intro y
    refine is_const_of_fderiv_eq_zero (f := fun y : Space => p (t, y) - Q (t, y))
      ((hdp t ht).sub hQd) (fun z => ?_) y 0
    rw [fderiv_fun_sub ((hdp t ht) z) (hQd z), hfd z, sub_self]
  have := hconst x
  linarith [this]

/-- **The contract field `ManuscriptLocalRegularity.pressure_potential` on `R³`
(`research/A01/Spec.lean:227-229`).**  For every classical whole-space solution
`u`, the pressure is gauge-equivalent on `Ico 0 T` to the radial potential of its
own gradient. -/
theorem pressure_potential_of_classicalSolution {ν : ℝ} {a : Space → Space}
    {f : VelocityField} {T : ℝ} (u : ClassicalSolutionR ν a f T) :
    PressureGaugeEquivOn (Ico (0 : ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2)) u.pressure := by
  refine pressure_potential_of_pointwise u.pressure (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht => ?_)
  · exact hasSymmetricJacobian_pressureGradient u.pressure_smooth ht
  · exact contDiff_gradSlice u.pressure_smooth ht
  · exact (NSFormalization.Section4.D01.contDiff_slice_scalar u.pressure_smooth ht).differentiable
      (by simp)

end NSFormalization.Section4.A01.PressureGauge
