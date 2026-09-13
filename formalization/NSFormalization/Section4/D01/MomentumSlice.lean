import NSFormalization.Section4.D01.Pressure
import NSFormalization.Section4.D01.DivergenceTime

/-!
# Momentum-slice regularity for eq:Rpressure (unit D01 / P2 sub-lemma SL8 preparation)

`research/D01/P2_SPLIT.md` sub-lemma **SL7b/SL8**, `research/D01/REVIEW_ORDER_ZERO.md` §6.4–6.5.
The eq:Rpressure assembly seeds order-0 data for `∇p(t,·)` and `∂ₜu(t,·)` and needs the pointwise
divergence-free / curl-free constraints of those two fields in the exact shapes the fibre facts
(`OrderZeroSymbol.orderZeroDatum_transverse_of_divergence_free` for `∂ₜu`; and, after lane 108
merged (PR #110), `Leray.lerayComplement_zero_orderZeroDatum_eq_self` for the order-0 curl-free
`∇p`) consume.  This module packages the pieces
that are cheap from `Section4/D01/Pressure.lean` (the momentum identities and the `H^∞` slices) and
`Section4/D01/DivergenceTime.lean` (`div ∂ₜu = 0`), on the classes `ClassicalSolutionR` /
`MemForceR`.

## What is proved

* `smoothL2_momentumResidual_slice` — the momentum residual `h = f − (u·∇)u + νΔu` slice is
  `SmoothL2` (`H^∞`).  This is the `h` with `∂ₜu = h − ∇p` that the SL8 table's rows i.2–i.4
  consume; it is factored out of the two `L²`/`C^∞` proofs below.
* `memLp_pressureGradient_slice` — `∇p(t,·) ∈ L²`, directly from `ClassicalSolutionR.pressure_gradient`
  restricted from `Ico 0 T` to the interior time.  (This is the order-0 seed for `∇p`.)
* `memLp_temporalDerivative_slice` — `∂ₜu(t,·) ∈ L²`, from the momentum rearrangement
  `∂ₜu = f − (u·∇)u + νΔu − ∇p` (`Pressure.temporalDerivative_slice_eq`): the first three terms
  are `H^∞` (hence `L²`) via `forceSlice_smoothL2_of_memForceR` / `advection_slice_smoothL2` /
  `laplacian_slice_smoothL2` + `A05.SmoothL2.memLp`, and `∇p` is `L²` by the field above.
* `contDiff_temporalDerivative_slice` — `∂ₜu(t,·)` is `C^∞` in space, from the same rearrangement
  with `contDiff_pressureGradient_slice` supplying the (cheap) spatial smoothness of `∇p`.
* `sum_partialDeriv_temporalDerivative_eq_zero` — `∑ⱼ ∂ⱼ(∂ₜu)ⱼ(t,·) = 0`, the pointwise
  divergence in the transverse-lemma shape.  It is `DivergenceTime`'s
  `spatialDivergence_temporalDerivative_eq_zero` in the `A03.partialDeriv` convention, which agrees
  by `rfl` (recorded in `research/D01/REVIEW_ORDER_ZERO.md` §6.5).
* `pressureGradient_apply` — the `j`-th component of `∇p` is the `j`-th spatial partial of the
  scalar pressure slice: `(∇p(t,·))ⱼ = ∂ⱼ(p(t,·))`.
* `partialDeriv_gradient_eq_sndFDeriv` — the `(i,j)` entry of the Jacobian of `∇p` is the second
  Fréchet derivative `D²(p(t,·)) x eᵢ eⱼ` of the scalar potential (component pull + the CLM
  chain rule twice).
* `partialDeriv_pressureGradient_symm` — hence the Jacobian of `∇p(t,·)` is **symmetric**
  (curl-free): `∂ᵢ(∇p)ⱼ = ∂ⱼ(∇p)ᵢ`.  This is Clairaut on the smooth scalar pressure slice
  (`ContDiffAt.isSymmSndFDerivAt`, the same in-tree route `DivergenceTime` uses for `div ∂ₜu`);
  lane 106's `hasSymmetricJacobian_pressureGradient` is **not** importable in this worktree, so the
  symmetry is proved directly (recorded in `research/D01/ATTEMPTS_SL8_PREP.md`).

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_sl8_prep.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)
open NSFormalization.Section4.A03 (partialDeriv)
open scoped ContDiff

/-! ## 1. `L²` and `C^∞` regularity of the momentum slices -/

/-- **The momentum residual `h = f − (u·∇)u + νΔu` slice is `H^∞`.**  Force slice
(`forceSlice_smoothL2_of_memForceR`), advection slice (`advection_slice_smoothL2`) and viscous slice
(`laplacian_slice_smoothL2`) combined by `smoothL2_add`/`smoothL2_sub`/`smoothL2_const_smul`.  This
is exactly the `h` with `∂ₜu = h − ∇p` (`temporalDerivative_slice_eq`) that the SL8 assembly's
rows i.2–i.4 consume (via `hres.memLp`); it is factored out of the two proofs below. -/
theorem smoothL2_momentumResidual_slice {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    A05.SmoothL2 (fun x : Space => f (t, x) - advection u.velocity t x
      + ν • spatialLaplacian u.velocity t x) :=
  smoothL2_add
    (smoothL2_sub (forceSlice_smoothL2_of_memForceR hf (le_of_lt ht.1))
      (advection_slice_smoothL2 u ht))
    (smoothL2_const_smul (laplacian_slice_smoothL2 u ht) ν)

/-- **`∇p(t,·) ∈ L²`.**  Directly from `ClassicalSolutionR.pressure_gradient`, restricting the
`Ico 0 T` membership to the interior time. -/
theorem memLp_pressureGradient_slice {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    MemLp (fun x : Space => pressureGradient u.pressure t x) 2 volume :=
  u.pressure_gradient t ⟨le_of_lt ht.1, ht.2⟩

/-- **`∂ₜu(t,·) ∈ L²`.**  From `temporalDerivative_slice_eq` (`∂ₜu = f − (u·∇)u + νΔu − ∇p`): the
force, advection and viscous slices are `H^∞` (hence `L²`) and `∇p` is `L²`. -/
theorem memLp_temporalDerivative_slice {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    MemLp (fun x : Space => temporalDerivative u.velocity t x) 2 volume := by
  have hpart := smoothL2_momentumResidual_slice u hf ht
  have hp : MemLp (fun x : Space => pressureGradient u.pressure t x) 2 volume :=
    u.pressure_gradient t ⟨le_of_lt ht.1, ht.2⟩
  have heq : (fun x : Space => temporalDerivative u.velocity t x)
      = fun x : Space => f (t, x) - advection u.velocity t x
          + ν • spatialLaplacian u.velocity t x - pressureGradient u.pressure t x := by
    funext x; exact temporalDerivative_slice_eq u ht x
  rw [heq]
  exact hpart.memLp.sub hp

/-- **`∂ₜu(t,·)` is `C^∞` in space.**  Same rearrangement, with the (cheap) spatial smoothness of
`∇p(t,·)` supplied by `contDiff_pressureGradient_slice`. -/
theorem contDiff_temporalDerivative_slice {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun x : Space => temporalDerivative u.velocity t x) := by
  have hpart := smoothL2_momentumResidual_slice u hf ht
  have hp : ContDiff ℝ ∞ (fun x : Space => pressureGradient u.pressure t x) :=
    contDiff_pressureGradient_slice u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩
  have heq : (fun x : Space => temporalDerivative u.velocity t x)
      = fun x : Space => f (t, x) - advection u.velocity t x
          + ν • spatialLaplacian u.velocity t x - pressureGradient u.pressure t x := by
    funext x; exact temporalDerivative_slice_eq u ht x
  rw [heq]
  exact hpart.1.sub hp

/-! ## 2. The pointwise divergence-free constraint on `∂ₜu` -/

/-- **`∑ⱼ ∂ⱼ(∂ₜu)ⱼ(t,·) = 0`.**  The pointwise divergence of the time-derivative slice, in the
`A03.partialDeriv` shape the transverse fibre fact
(`OrderZeroSymbol.orderZeroDatum_transverse_of_divergence_free`) consumes.  It is
`DivergenceTime.spatialDivergence_temporalDerivative_eq_zero` — the two agree by `rfl`. -/
theorem sum_partialDeriv_temporalDerivative_eq_zero {ν : ℝ} {a : Space → Space}
    {f : VelocityField} {T : ℝ} (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (x : Space) :
    ∑ j : Fin 3, partialDeriv j (fun y : Space => temporalDerivative u.velocity t y) x j = 0 :=
  DivergenceTime.spatialDivergence_temporalDerivative_eq_zero u ht x

/-! ## 3. The curl-free (symmetric-Jacobian) constraint on `∇p` -/

/-- **The `j`-th component of `∇p` is the `j`-th spatial partial of the scalar pressure slice.**
`(∇p(t,·))ⱼ = ∂ⱼ(p(t,·))`, unfolding `pressureGradient = ∑ᵢ (∂ᵢp) eᵢ` and reading off the
`j`-th Euclidean coordinate. -/
theorem pressureGradient_apply (p : PressureField) (t : ℝ) (y : Space) (j : Fin 3) :
    pressureGradient p t y j = fderiv ℝ (fun z : Space => p (t, z)) y (coordinateVector j) := by
  rw [pressureGradient, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [coordinateVector, WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j]
  simp

/-- **The Jacobian entry of `∇p` is a second derivative of the scalar potential.**
`∂ᵢ(∇p)ⱼ = D²(p(t,·)) x eᵢ eⱼ`.  Pull the `j`-th coordinate through the outer derivative and the
`i`-th spatial partial through the evaluation `L ↦ L eⱼ`, both by the CLM chain rule, then use
`pressureGradient_apply` to identify the middle function. -/
theorem partialDeriv_gradient_eq_sndFDeriv (p : PressureField) (t : ℝ)
    (hφ : ContDiff ℝ ∞ (fun z : Space => p (t, z)))
    (i j : Fin 3) (x : Space) :
    partialDeriv i (fun y : Space => pressureGradient p t y) x j
      = fderiv ℝ (fderiv ℝ (fun z : Space => p (t, z))) x
          (coordinateVector i) (coordinateVector j) := by
  have hpd : partialDeriv i (fun y : Space => pressureGradient p t y) x
      = fderiv ℝ (fun y : Space => pressureGradient p t y) x (coordinateVector i) := rfl
  have hd : ContDiff ℝ ∞ (fun y : Space => fderiv ℝ (fun z : Space => p (t, z)) y) :=
    hφ.fderiv_right (m := ∞) (by simp)
  have hg : ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y) := by
    refine ContDiff.sum (fun k _ => ?_)
    exact ContDiff.smul
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).contDiff.comp hd) contDiff_const
  have hgd : DifferentiableAt ℝ (fun y : Space => pressureGradient p t y) x :=
    (hg.differentiable (by simp)).differentiableAt
  have hfφd : DifferentiableAt ℝ (fderiv ℝ (fun z : Space => p (t, z))) x :=
    ((hφ.fderiv_right (m := 1) (by simp)).differentiable (by simp)).differentiableAt
  have hfun : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)
        ∘ (fun y : Space => pressureGradient p t y)
      = (ContinuousLinearMap.apply ℝ ℝ (coordinateVector j))
          ∘ (fderiv ℝ (fun z : Space => p (t, z))) := by
    funext y
    simp only [Function.comp_apply, PiLp.proj_apply, ContinuousLinearMap.apply_apply]
    exact pressureGradient_apply p t y j
  have hL := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp x
    hgd.hasFDerivAt).fderiv
  have hRr := ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector j)).hasFDerivAt.comp x
    hfφd.hasFDerivAt).fderiv
  have hchain : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).comp
        (fderiv ℝ (fun y : Space => pressureGradient p t y) x)
      = (ContinuousLinearMap.apply ℝ ℝ (coordinateVector j)).comp
          (fderiv ℝ (fderiv ℝ (fun z : Space => p (t, z))) x) := by
    rw [← hL, ← hRr]
    exact congrArg (fun h => fderiv ℝ h x) hfun
  have happ := congrArg (fun L => L (coordinateVector i)) hchain
  simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    ContinuousLinearMap.apply_apply] at happ
  rw [hpd]
  exact happ

/-- **The Jacobian of `∇p(t,·)` is symmetric (`∇p` is curl-free).**
`∂ᵢ(∇p)ⱼ = ∂ⱼ(∇p)ᵢ`.  This is the `hcurl` shape consumed at order 0 by lane 108's
`Leray.lerayComplement_zero_orderZeroDatum_eq_self` (bare `MemLp`); the superficially matching
`Longitudinal.lerayComplement_eq_self_of_curl_free` cannot be applied here — it needs a
`SmoothL2Field` and order `(m:ℝ)+1`, never `0`.  Proved by Clairaut on the smooth scalar pressure
slice, via `ContDiffAt.isSymmSndFDerivAt` (the in-tree route `DivergenceTime` uses for `div ∂ₜu`);
lane 106's more general `hasSymmetricJacobian_pressureGradient` is not importable in this worktree
(its `.2 x i j` is the `rfl`-equal drop-in after rebase). -/
theorem partialDeriv_pressureGradient_symm {ν : ℝ} {a : Space → Space} {f : VelocityField}
    {T : ℝ} (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (i j : Fin 3) (x : Space) :
    partialDeriv i (fun y : Space => pressureGradient u.pressure t y) x j
      = partialDeriv j (fun y : Space => pressureGradient u.pressure t y) x i := by
  have hφ : ContDiff ℝ ∞ (fun z : Space => u.pressure (t, z)) :=
    contDiff_slice_scalar u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩
  have hφ2 : ContDiffAt ℝ 2 (fun z : Space => u.pressure (t, z)) x :=
    hφ.contDiffAt.of_le (by norm_num)
  rw [partialDeriv_gradient_eq_sndFDeriv u.pressure t hφ i j x,
      partialDeriv_gradient_eq_sndFDeriv u.pressure t hφ j i x]
  exact (hφ2.isSymmSndFDerivAt (by norm_num)).eq (coordinateVector i) (coordinateVector j)

end NSFormalization.Section4.D01
