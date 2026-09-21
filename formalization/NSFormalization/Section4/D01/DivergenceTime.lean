import NSFormalization.Section4.A02.SolutionClass
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# D01 · P2 sub-lemma SL4α: the time-derivative slice of a classical solution is divergence-free

`research/D01/P2_SPLIT.md` sub-lemma **SL4α**.  For a classical whole-space solution
`u : ClassicalSolutionR ν a f T` (`Section4/A02/SolutionClass.lean`), the manuscript's
time-derivative slice `∂ₜu(t,·)` inherits the divergence-free constraint of `u`:
```
div (∂ₜu) (t, x) = ∂ₜ (div u) (t, x) = ∂ₜ 0 = 0    on  Ioo 0 T.
```
The one analytic ingredient is the commutation of the time derivative with each spatial
partial derivative — Clairaut / symmetry of the second Fréchet derivative of the jointly
`C²` velocity field on the open slab `Ioo 0 T ×ˢ univ`.

## What is proved

* `spatialDivergence_temporalDerivative_eq_zero` — the classical statement:
  `spatialDivergence (fun p => temporalDerivative u.velocity p.1 p.2) t x = 0` for every
  `t ∈ Ioo 0 T` and every `x`.

## Method

`div u (s, x) = ∑ᵢ (fderiv ℝ (y ↦ u(s,y)) x eᵢ) i` is identically `0` for `s ∈ Ico 0 T`
(field `ClassicalSolutionR.divergence`), so, as a function of time, it has derivative `0`
at every interior `t`.  Independently, the map `s ↦ fderiv ℝ (y ↦ u(s,y)) x` is
differentiable in `s` at `t` with derivative `fderiv ℝ (y ↦ ∂ₜu(t,y)) x`
(`spatial_fderiv_hasDerivAt`, the mixed-partial commutation, via
`ContDiffAt.isSymmSndFDerivAt`), so `s ↦ div u(s,x)` also has derivative
`∑ᵢ (fderiv ℝ (y ↦ ∂ₜu(t,y)) x eᵢ) i = div (∂ₜu)(t,x)`.  Uniqueness of the derivative
(`HasDerivAt.unique`) forces `div (∂ₜu)(t,x) = 0`.

The three mixed-derivative helpers `fderiv_spatial_slice`, `deriv_time_slice`,
`spatial_fderiv_hasDerivAt` are pure-Mathlib statements about a map `ℝ × Space → Space`.
They are a **literal copy** of the vendored
`Euler.ComparatorBridge.{fderiv_spatial_slice, deriv_time_slice, spatial_fderiv_hasDerivAt}`
(`vendor/NavierStokesAndEuler/Euler/CurlTimeDerivative.lean:14,25,33`) — this is the re-sync
point should the vendor pin change.  They are kept local rather than imported because importing
`Euler.*` would pull in ~6 modules / ~21.9k lines (incl. `Euler.EulerProof`); this module instead
imports only the canonical A02 restatement (`Section4/A02/SolutionClass.lean`) plus Mathlib, and
the operators `spatialDivergence` / `temporalDerivative` reach it through A02 from
`NavierStokes.ProblemStatement` (the module does not itself import `NavierStokes.R3.ProblemStatement`).

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_sl4a.lean`).
-/

noncomputable section

open Set Filter
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open scoped ContDiff Topology

namespace NSFormalization.Section4.D01.DivergenceTime

/-! ## 1. Mixed-derivative commutation helpers (pure Mathlib) -/

/-- The spatial Fréchet derivative of a time-slice is the spatial restriction of the joint
derivative. -/
theorem fderiv_spatial_slice {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ u (t, x)) :
    fderiv ℝ (fun y => u (t, y)) x =
      (fderiv ℝ u (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have h := hu.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  rw [show (fun y => u (t, y)) = u ∘ (fun y => (t, y)) from rfl, h.fderiv]
  congr 1

/-- The ordinary time derivative of a time-slice is the time direction of the joint
derivative. -/
theorem deriv_time_slice {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ u (t, x)) :
    deriv (fun r => u (r, x)) t = fderiv ℝ u (t, x) (1, 0) := by
  have h := hu.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simpa only [Function.comp_def, id_eq] using h.deriv

/-- **Mixed differentiation commutes** using only local joint `C²` regularity: the time
derivative of the spatial-derivative slice `r ↦ fderiv ℝ (y ↦ u(r,y)) x` is the spatial
derivative of the time-derivative slice `y ↦ ∂ₜu(t,y)`. -/
theorem spatial_fderiv_hasDerivAt {u : ℝ × Space → Space} {t : ℝ} {x : Space}
    (hu : ContDiffAt ℝ 2 u (t, x)) :
    HasDerivAt (fun r => fderiv ℝ (fun y => u (r, y)) x)
      (fderiv ℝ (fun y => deriv (fun r => u (r, y)) t) x) t := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) (t, x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : ∀ᶠ z in 𝓝 (t, x), DifferentiableAt ℝ u z := by
    filter_upwards [(hu.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num)]
      with z hz
    exact hz.differentiableAt (by norm_num)
  have htime := hdu.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hmatrix := htime.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ Space))
  have hspatial := hdu.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have hvelocity := hspatial.clm_apply (hasFDerivAt_const (1, (0 : Space)) x)
  have heq : (fun y => deriv (fun r => u (r, y)) t) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u (t, y) (1, 0)) := by
    filter_upwards [((continuous_const.prodMk continuous_id).tendsto x).eventually hnear]
      with y hy
    exact deriv_time_slice hy
  have hvelocity' := hvelocity.congr_of_eventuallyEq heq
  have hderiv : fderiv ℝ (fun y => deriv (fun r => u (r, y)) t) x =
      ((fderiv ℝ (fderiv ℝ u) (t, x)) (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space) := by
    rw [hvelocity'.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    simpa using hu.isSymmSndFDerivAt (by norm_num) (0, v) (1, 0)
  rw [hderiv]
  have hmatrix' : HasDerivAt (fun r => (fderiv ℝ u (r, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space))
      (((fderiv ℝ (fderiv ℝ u) (t, x)) (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) t := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_zero, add_zero] using hmatrix
  apply hmatrix'.congr_of_eventuallyEq
  filter_upwards [((continuous_id.prodMk continuous_const).tendsto t).eventually hnear]
    with r hr
  exact fderiv_spatial_slice hr

/-! ## 2. `div ∂ₜu = 0` on the interior slab -/

/-- **SL4α.**  The time-derivative slice `∂ₜu(t,·)` of a classical whole-space solution is
divergence-free at every interior time. -/
theorem spatialDivergence_temporalDerivative_eq_zero
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    spatialDivergence (fun p : SpaceTime => temporalDerivative u.velocity p.1 p.2) t x = 0 := by
  -- joint `C²` (indeed `C^∞`) regularity at the interior point `(t, x)`
  have hnhds : Ico (0 : ℝ) T ×ˢ (univ : Set Space) ∈ 𝓝 ((t, x) : SpaceTime) := by
    apply mem_nhds_iff.mpr
    refine ⟨Ioo (0 : ℝ) T ×ˢ (univ : Set Space), ?_, isOpen_Ioo.prod isOpen_univ,
      ⟨ht, mem_univ x⟩⟩
    exact Set.prod_mono Ioo_subset_Ico_self subset_rfl
  have hcda2 : ContDiffAt ℝ 2 u.velocity (t, x) :=
    (u.velocity_smooth.contDiffAt hnhds).of_le (by simp)
  have hswap := spatial_fderiv_hasDerivAt hcda2
  -- each diagonal entry of the mixed-derivative matrix has the expected time derivative
  have hcomp : ∀ i : Fin 3,
      HasDerivAt (fun s => (fderiv ℝ (fun y => u.velocity (s, y)) x (coordinateVector i)) i)
        ((fderiv ℝ (fun y => deriv (fun r => u.velocity (r, y)) t) x (coordinateVector i)) i) t := by
    intro i
    have h1 : HasDerivAt
        (fun s => (fderiv ℝ (fun y => u.velocity (s, y)) x) (coordinateVector i))
        (fderiv ℝ (fun y => deriv (fun r => u.velocity (r, y)) t) x (coordinateVector i)) t := by
      simpa only [map_zero, add_zero]
        using hswap.clm_apply (hasDerivAt_const t (coordinateVector i))
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt t h1
  -- `s ↦ div u(s,x)` has time derivative `div (∂ₜu)(t,x)`
  have hsum : HasDerivAt (fun s => spatialDivergence u.velocity s x)
      (spatialDivergence (fun p : SpaceTime => temporalDerivative u.velocity p.1 p.2) t x) t :=
    HasDerivAt.sum (fun (i : Fin 3) (_ : i ∈ Finset.univ) => hcomp i)
  -- and it is identically `0` on `Ico 0 T`, a neighbourhood of `t`
  have hzero : HasDerivAt (fun s => spatialDivergence u.velocity s x) 0 t := by
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ico_mem_nhds_iff.mpr ht] with s hs
    exact u.divergence s hs x
  exact hsum.unique hzero

end NSFormalization.Section4.D01.DivergenceTime
