# T20 U10a — attempts (lane 429, 2026-09-18)

Target: the mean-zero `H¹` trilinear estimate `|⟪(v·∇)v,Δv⟫| ≤ C₁ y ‖Δv‖₂²`
(`paper/sections/03-torus.tex:467-477`), the lemma `hOneEnergy` (U10b) consumes.
Delivered in `formalization/NSFormalization/Section3/T20/H1Trilinear.lean`.
Closed completely; no named input, no residual, no `sorry`/`axiom`.

Constant: `h1TrilinearConst = CcriticalHalf * Csix`
(`= T12.CcriticalHalf`, the order-`1/2` critical `L³` constant of T12 U4,
times `T12.Csix = 343 · A05.gradientL6Const · leibnizConst · (1 + 2·hTwoConst)`,
the `L⁶` gradient constant of T12 U5), with `h1TrilinearConst_pos`.

## Route actually taken

Exactly the brief's route, and it closed on the first mathematical attempt:

1. pointwise `‖⟪(v·∇)v(x), Δv x⟫‖ₑ ≤ ‖v x‖ₑ ‖∇v x‖ₑ ‖Δv x‖ₑ` — lane 413's
   `enorm_inner_advection_le` is already stated for an *arbitrary* second factor
   `Lv`, so `Lv := laplacian v` needs nothing new;
2. three-factor Hölder with exponents `(3, 6, 2)` directly against
   `periodicTorusMeasure` (no `HaarCube` transfer — see `ATTEMPTS_U7.md`), via
   Mathlib `ENNReal.lintegral_prod_norm_pow_le` with the exponent vector
   `![1/3, 1/6, 1/2]`;
3. `T12.velocityCriticalL3` (`‖v‖₃ ≤ CcriticalHalf·y`) and `T12.gradientLSix`
   (`‖∇v‖₆ ≤ Csix·‖Δv‖₂`), both already in the exact `periodicLpENorm`
   spellings step 2 produces.

**The brief's optional Fourier step `‖∇(∂ⱼv)‖₂ ≤ ‖Δv‖₂` (`:475-477`) is not
needed.**  Checked first, as instructed: `T12.gradientLSix` (lane 400) is stated
as `periodicLpENorm 6 (gradientTensor v) ≤ ENNReal.ofReal Csix *
periodicLpENorm 2 (laplacian v)` — the input spelling `gradientTensor v` is
literally the one §1 hands it, and the per-derivative Fourier comparison is
already internal to lane 400's proof (`periodicLpENorm_gradientTensor_le_laplacian`,
`GradientLSix.lean:167`).  Nothing about it had to be re-derived.

## The one real obstacle: a duplicate declaration blocks the intended import

**First attempt** imported `Section3.T20.CriticalTrilinear` (to reuse lane 413's
machinery, as the brief asks) **and** `Section3.T12.GradientLSix` (for
`gradientLSix`).  That is impossible in the current tree:

```
error: NSFormalization/Section3/T20/H1Trilinear.lean:1:0: import
NSFormalization.Section3.T12.GradientLSix failed, environment already contains
'NSFormalization.Section3.T12.contDiff_dirDeriv'
from NSFormalization.Section3.T12.GradientLambdaL3
```

`NSFormalization.Section3.T12.contDiff_dirDeriv` is declared **twice**:

- `Section3/T12/GradientLSix.lean:184` (lane 400), general target
  `{w : Space → F}` with `[NormedAddCommGroup F] [NormedSpace ℝ F]`;
- `Section3/T12/GradientLambdaL3.lean:210` (lane 405), specialized to
  `{v : SpatialField}`.

The proof is the same line in both (`(hs.fderiv_right (by simp)).clm_apply
contDiff_const`), and the lane-400 version subsumes the lane-405 one.  They were
merged from separate lanes and have never been co-imported.  A diff of all
declaration names in the two modules shows `contDiff_dirDeriv` is the **only**
collision:

```
$ comm -12 <(names GradientLSix.lean) <(names GradientLambdaL3.lean)
contDiff_dirDeriv
```

`CriticalTrilinear` imports `GradientLambdaL3` (it needs
`gradientLambdaCriticalL3`), so *any* module needing both `gradientLSix` and
anything downstream of `GradientLambdaL3` is currently unbuildable.

**Resolution inside the lane's authority** (no edits to existing modules): the
module sits on the `GradientLSix` side —
`import CriticalRegularity + CriticalL3Density + GradientLSix`, which is
collision-free (`CriticalL3Density` imports `CriticalL3`, not
`GradientLambdaL3`) — and §0 repeats lane 413's four small helpers under
`…H1`-suffixed names (`measurable_torusChartH1`,
`aestronglyMeasurable_torusLiftH1`, `continuous_gradientTensorH1`,
`enorm_inner_advection_leH1`; ~35 lines total, unchanged proofs).  The suffixed
names are distinct from lane 413's, so `H1Trilinear` and `CriticalTrilinear`
will import together the moment the duplicate is removed, and every declaration
stays individually `#print axioms`-auditable.  The Hölder **engine** is not
copied: §1 is a fresh exponent instance `(3,6,2)`, not a re-proof of `(3,3,3)`.

**This is a lead-level item, not a lane-level one.**  U10b needs U10a
(`GradientLSix` side) *and* U9/U8/U7 (`GradientLambdaL3` side), and U13 needs
everything, so the duplicate must be deleted upstream before T20 can be
assembled.  Minimal fix: delete `contDiff_dirDeriv` from
`GradientLambdaL3.lean:210-212` and let it import `GradientLSix` (or move the
general version into `MeanZeroCalculus`/`FourierEmbeddings`, which both modules
already import).  Either is an edit to a merged module, hence out of this lane's
scope.

## Failed tactic attempts (Lean-level, all fixed)

- `norm_num [Fin.sum_univ_three]` for the exponent-sum side condition
  `∑ i, ![1/3, 1/6, 1/2] i = 1` **fails**:

  ```
  error: NSFormalization/Section3/T20/H1Trilinear.lean:206:10: unsolved goals
  case refine_2
  ⊢ 1 / 2 + ![1 / 3, 1 / 6, 1 / 2] 2 = 1
  ```

  `norm_num` evaluates `![…] 0` and `![…] 1` (they reduce through
  `Matrix.cons_val_zero`/`cons_val_one`, which are `simp`) but **not** `![…] 2`,
  which needs `Matrix.cons_val_two` + `Matrix.head_cons`/`tail_cons`.  Lane 413
  never saw this because its exponent vector was the constant `fun _ ↦ 1/3`,
  written out literally three times.  Fix: `simp only [Fin.sum_univ_three,
  Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
  Matrix.head_cons, Matrix.tail_cons]` then `norm_num`.  The positivity side
  condition `0 ≤ p i` has the same hazard and is discharged with
  `fin_cases i <;> norm_num`.

- No other failures: the `(3,6,2)` `eLpNorm` conversions
  (`eLpNorm_eq_lintegral_rpow_enorm_toReal` + `ENNReal.toReal_ofNat`) behave the
  same at `6` and `2` as at `3`; `ENNReal.ofReal_mul CcriticalHalf_pos.le` closes
  the constant split in one line (only two factors here, so the
  `← mul_assoc`-first dance of lane 413 is unnecessary); `laplacianSqT` being a
  plain `def` is absorbed by `exact` (delta), so `h1Trilinear` is one term.

## Deliverables and gates

- `formalization/NSFormalization/Section3/T20/H1Trilinear.lean` — 16 declarations,
  `lake build` 0 errors, `lake env lean` 0 bytes of output.
- `research/T20/probes/h1_trilinear_closes.lean` — nonzero witness
  `probeMZ = meanZeroPartT (x ↦ cos(2πx₀)·e₀)` with the estimate instantiated
  there, `‖Δ probeMZ‖₂ ≠ ⊤`, and the U10b slice shape check
  `fun x ↦ meanFreeVelocity g u (t, x)` in the `criticalY`/`laplacianSqT`
  spelling.  0 bytes of output.
- `research/T20/axioms_u10a.lean` — all 16 declarations print exactly
  `[propext, Classical.choice, Quot.sound]`.
