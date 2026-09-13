import NSFormalization.Section4.A02.SolutionClass

/-!
# R42, item 1f: the `pressure_gradient` clause for the inserted pressure `p_ε = π + P_ε`

Theorem 4.2 of `paper/sections/04-whole-space.tex` (lines 32-38, 53) inserts, on
top of the reference solution `(v, π)`, a velocity correction `u_ε = v + w_ε + U_ε`
and a *pressure* correction, giving the inserted pressure `p_ε = π + P_ε`, where
`P_ε = p_ε − π` is supported (in space, at each time) inside the fixed ball
`B(x₀, r)`.  Inhabiting `Data.ClassicalSolutionR ν a g_ε S` (`A02.ClassicalSolutionR`)
requires its `pressure_gradient` field
(`A02/SolutionClass.lean:137`, `Contracts/V1/Data.lean`):

  `∀ t ∈ Ico 0 S, MemLp (fun x => pressureGradient p_ε t x) 2 volume`.

`research/R42/LIFESPAN_SPLIT.md` item **1f** reduces this to a gradient-slice
`L²` additivity: `∇π = ∇(reference.pressure)` is the reference's own
`pressure_gradient`, and `∇P_ε` has compact spatial support, hence is in `L²`.

This module discharges that residual with two lemmas and one corollary, importing
only `A02.SolutionClass` (for the field shape and the `pressureGradient`
abbreviation via `open NavierStokes.ProblemStatement`) and Mathlib:

* `memLp_pressureGradient_of_compact` — the smoothness/measure unit.  The gradient
  of a spatially compactly supported smooth slice is in `L²`.  The slice
  `q := fun x => P (t,x)` is `ContDiff ℝ ∞` (compose the field's `ContDiffOn` on
  `Ico 0 T ×ˢ univ` with the affine inclusion `x ↦ (t,x)`, which lands in the slab
  since `t ∈ Ico 0 T`; this is a byte-identical inline copy of
  `D01/DatumToJets.lean:377`'s `contDiff_slice_scalar`).  Its Fréchet derivative is continuous
  (`ContDiff.continuous_fderiv`) and vanishes off `tsupport q`
  (`Filter.EventuallyEq.fderiv_eq` against the locally-zero slice), so
  `x ↦ pressureGradient P t x` is continuous with support inside the closed ball,
  hence `MemLp … 2` by `Continuous.memLp_of_hasCompactSupport`.

* `memLp_pressureGradient_add` — the additivity unit.  For `p = π + P`
  (pointwise, as functions on `ℝ × Space`) the gradients add:
  `pressureGradient (π+P) t = pressureGradient π t + pressureGradient P t`
  (`fderiv_add` on the differentiable slices, `add_apply`, `add_smul`,
  `Finset.sum_add_distrib`), so `MemLp.add` closes it.

* `memLp_pressureGradient_of_difference_support` — the corollary the consumer
  (the R42 assembly) calls.  From the reference's `pressure_gradient` for `π`,
  smoothness of `p_ε`, and `tsupport (p_ε(t,·) − π(t,·)) ⊆ B(x₀,r)`, write
  `p_ε = π + (p_ε − π)`, apply the compact-support unit to `p_ε − π` and the
  additivity unit to the pair.

The statement is kept at a single horizon `T` (the consumer restricts the larger
reference horizon `T'` down to the correction horizon `S ≤ T'` before applying
`memLp_pressureGradient_of_difference_support`).
-/

noncomputable section

namespace NSFormalization.Section4.R42

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open scoped ContDiff ENNReal

/-- A spatial slice `x ↦ p(t,x)` of a scalar field smooth on the closed-at-zero
slab `[0,T) × ℝ³` is smooth on all of `ℝ³`, **including at `t = 0`**: the slab
still contains a full spatial neighbourhood of every `(t,x)` with `t ∈ [0,T)`, so
composing with the affine inclusion `x ↦ (t,x)` lands the data on a genuine slice
neighbourhood.  This is the scalar case of `D01/DatumToJets.lean:377`'s
`contDiff_slice_scalar`, inlined here to keep this module's import surface to
`A02.SolutionClass` + Mathlib.  Named `_pressure` (not `contDiff_slice`) so that it
neither shadows nor is confused with D01's vector-valued `contDiff_slice` when both
namespaces are open. -/
theorem contDiff_slice_pressure {T : ℝ} {p : ℝ × Space → ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ fun x : Space => p (t, x) := by
  rw [← contDiffOn_univ]
  have hmap : ContDiffOn ℝ ∞ (fun x : Space => (t, x)) (univ : Set Space) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hsub : (univ : Set Space) ⊆
      (fun x : Space => (t, x)) ⁻¹' (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    fun x _ => ⟨ht, mem_univ x⟩
  exact hp.comp hmap hsub

/-- **Item 1f, compact-support unit (S–M).**  The Euclidean gradient of a
spatially compactly supported smooth slice is square integrable: if `P` is smooth
on `[0,T) × ℝ³` and its slice `x ↦ P(t,x)` is supported in `B(x₀,r)` at the fixed
time `t ∈ [0,T)`, then `x ↦ pressureGradient P t x` is in `L²`.

`x ↦ pressureGradient P t x` is a finite sum of `smul`s of continuous functions
(`ContDiff.continuous_fderiv`), and it vanishes off `tsupport (P(t,·))` because the
slice is locally zero there (`Filter.EventuallyEq.fderiv_eq`); so it is continuous
with support inside the compact `closedBall x₀ r`, and
`Continuous.memLp_of_hasCompactSupport` applies. -/
theorem memLp_pressureGradient_of_compact {P : ℝ × Space → ℝ} {T : ℝ} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T)
    (hP : ContDiffOn ℝ ∞ P (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    {x₀ : Space} {r : ℝ} (hsupp : tsupport (fun x => P (t, x)) ⊆ Metric.ball x₀ r) :
    MemLp (fun x => pressureGradient P t x) 2 volume := by
  have hq : ContDiff ℝ ∞ (fun x : Space => P (t, x)) := contDiff_slice_pressure hP ht
  have hfd : Continuous (fderiv ℝ (fun x : Space => P (t, x))) := hq.continuous_fderiv (by decide)
  -- The gradient's support sits inside the slice's `tsupport`: off it the slice is
  -- locally zero, so its Fréchet derivative, hence every summand, vanishes.
  have hsupp_g : Function.support (fun x : Space => pressureGradient P t x) ⊆
      tsupport (fun x : Space => P (t, x)) := by
    intro x hx
    by_contra hxns
    apply hx
    have hz : (fun x : Space => P (t, x)) =ᶠ[𝓝 x] (fun _ => 0) := by
      have hopen : IsOpen (tsupport (fun x : Space => P (t, x)))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      filter_upwards [hopen.mem_nhds hxns] with y hy
      exact image_eq_zero_of_notMem_tsupport (f := fun x : Space => P (t, x)) hy
    have hfd0 : fderiv ℝ (fun x : Space => P (t, x)) x = 0 := by
      rw [hz.fderiv_eq]; simp
    show pressureGradient P t x = 0
    unfold pressureGradient
    rw [hfd0]
    simp
  have hcs : HasCompactSupport (fun x : Space => pressureGradient P t x) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ r)
      (hsupp_g.trans (hsupp.trans Metric.ball_subset_closedBall))
  have hcont : Continuous (fun x : Space => pressureGradient P t x) := by
    unfold pressureGradient
    apply continuous_finsetSum
    intro i _
    exact (hfd.clm_apply continuous_const).smul continuous_const
  exact hcont.memLp_of_hasCompactSupport hcs

/-- **Item 1f, additivity unit (S).**  For `p = π + P` (pointwise, as functions on
`ℝ × Space`), the Euclidean gradient is additive at each fixed time, so
`∇p ∈ L²` follows from `∇π ∈ L²` and `∇P ∈ L²` by `MemLp.add`.

Pointwise `pressureGradient (π+P) t = pressureGradient π t + pressureGradient P t`
by `fderiv_add` on the (smooth, hence differentiable) slices, distributing the
finite sum. -/
theorem memLp_pressureGradient_add {π P : ℝ × Space → ℝ} {T : ℝ} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T)
    (hπ : ContDiffOn ℝ ∞ π (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hP : ContDiffOn ℝ ∞ P (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (h1 : MemLp (fun x => pressureGradient π t x) 2 volume)
    (h2 : MemLp (fun x => pressureGradient P t x) 2 volume) :
    MemLp (fun x => pressureGradient (fun z => π z + P z) t x) 2 volume := by
  have hπq : ContDiff ℝ ∞ (fun x : Space => π (t, x)) := contDiff_slice_pressure hπ ht
  have hPq : ContDiff ℝ ∞ (fun x : Space => P (t, x)) := contDiff_slice_pressure hP ht
  have hpt : ∀ x, pressureGradient (fun z => π z + P z) t x
      = pressureGradient π t x + pressureGradient P t x := by
    intro x
    have hdπ : DifferentiableAt ℝ (fun y : Space => π (t, y)) x :=
      (hπq.differentiable (by decide)).differentiableAt
    have hdP : DifferentiableAt ℝ (fun y : Space => P (t, y)) x :=
      (hPq.differentiable (by decide)).differentiableAt
    have hkey : fderiv ℝ (fun y : Space => π (t, y) + P (t, y)) x
        = fderiv ℝ (fun y : Space => π (t, y)) x + fderiv ℝ (fun y : Space => P (t, y)) x :=
      fderiv_add hdπ hdP
    simp only [pressureGradient]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hkey, add_apply, add_smul]
  have hfun : (fun x => pressureGradient (fun z => π z + P z) t x)
      = (fun x => pressureGradient π t x + pressureGradient P t x) := funext hpt
  rw [hfun]
  exact h1.add h2

/-- **Item 1f, the consumer's corollary (M).**  This is exactly the
`pressure_gradient` clause of `ClassicalSolutionR` for the inserted pressure
`p_ε = π + P_ε`.  Given the reference's own `pressure_gradient` (`h1`, for `π`),
smoothness of the inserted pressure `p` and of `π`, and the localization of the
pressure difference `p(t,·) − π(t,·)` in a fixed ball, `∇p ∈ L²`.

Route: `p = π + (p − π)`; the compact-support unit gives `∇(p − π) ∈ L²`, and the
additivity unit combines it with `h1`. -/
theorem memLp_pressureGradient_of_difference_support {π p : ℝ × Space → ℝ} {T : ℝ} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T)
    (hπ : ContDiffOn ℝ ∞ π (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (h1 : MemLp (fun x => pressureGradient π t x) 2 volume)
    {x₀ : Space} {r : ℝ}
    (hsupp : tsupport (fun x => p (t, x) - π (t, x)) ⊆ Metric.ball x₀ r) :
    MemLp (fun x => pressureGradient p t x) 2 volume := by
  have hPsub : ContDiffOn ℝ ∞ (fun z => p z - π z) (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    hp.sub hπ
  have h2 : MemLp (fun x => pressureGradient (fun z => p z - π z) t x) 2 volume :=
    memLp_pressureGradient_of_compact ht hPsub hsupp
  have hadd := memLp_pressureGradient_add ht hπ hPsub h1 h2
  -- `p = π + (p − π)`; rewriting the (single) pressure argument in the goal to this
  -- sum turns the goal into `hadd`'s conclusion (defeq up to the residual beta-redex).
  have heq : p = (fun z : ℝ × Space => π z + (p z - π z)) := by funext z; ring
  rw [heq]
  exact hadd

end NSFormalization.Section4.R42
