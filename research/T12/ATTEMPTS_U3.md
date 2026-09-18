# T12 U3 — cutoff–Gagliardo comparison at `a = 1/2` (lane 377)

Target (`research/T12/T12_SPLIT.md` U3, `appendix-b-embeddings.tex`,
`03-torus.tex`): for smooth mean-zero periodic `v`,
`dotHomogeneousENorm (1/2) (cutoffMul v) ≤ ENNReal.ofReal cutoffGagliardoConst ·
(eLpNorm v 2 (volume.restrict fundamentalCube) + periodicHomogeneousENorm (1/2) v)`.

**Status: fully proved.**  `Section3/T12/CutoffGagliardo.lean`, theorem
`cutoff_gagliardo_half`, with explicit positive constant
`cutoffGagliardoConst = max (√(2·343)) (√(2·cbConst / cFrac (1/2)))`
(`cbConst = 686 · Jval.toReal`).  Every declaration carries exactly
`[propext, Classical.choice, Quot.sound]`.

## Structure of the proof (module `Section3/T12/CutoffGagliardo.lean`)

Reduction backbone:
1. `meanZeroPartT_eq_self` : `IsMeanZeroT v → meanZeroPartT v = v`.
2. `cFrac_half_pos/_lt_top/_ne_zero/_ne_top` : `0 < cFrac (1/2) < ⊤`
   (T13 `constant_pos_finite`).
3. `ireal_cutoffMul_eq` : `IReal (1/2) (cutoffMul v)
   = cFrac (1/2) · dotHomogeneousENorm (1/2) (cutoffMul v) ^ 2`
   — `wholeSpace_identity` at `s = 1/2`, `cutoffMul v` smooth
   (`contDiff_cutoffMul`) + compactly supported (`hasCompactSupport_cutoffMul`).
4. `itorus_meanZero_eq` : `ITorus (1/2) v
   = cFrac (1/2) · periodicHomogeneousENorm (1/2) v ^ 2`
   — `torus_identity_smooth` at `s = 1/2` then `meanZeroPartT v = v`.
5. `enn_sqrt_div_bound` : the `ℝ≥0∞` divide-by-`cFrac` + square-root step.
6. `gA/gB/IA/IB`, `lintegral_two_add_two`, `measurable_gA_pair/_gB_pair`,
   `ireal_cutoffMul_le_split` : the difference split
   `χ(x+h)v(x+h) − χ(x)v(x) = χ(x+h)(v(x+h)−v(x)) + (χ(x+h)−χ(x))v(x)`,
   `‖a+b‖² ≤ 2‖a‖²+2‖b‖²`, giving `IReal (1/2) (χv) ≤ 2·IA v + 2·IB v`.
7. `dotHomogeneousENorm_cutoffMul_le` : assembly from the two kernel bounds.

The two localization kernel bounds (the analytic core):
- `iA_bound : IA v ≤ ENNReal.ofReal 343 · ITorus (1/2) v`.  Tonelli swap +
  change of variables `(x,h) ↦ (x, y=x+h)`; `‖χ(y)•(v(y)-v(x))‖² =
  χ(y)²‖v(y)-v(x)‖²`; fold the whole `x`-integral onto the cube via
  `lintegral_cube_periodicKernel` (produces `periodicKernel`); tile the outer
  `y`-integral (`lintegral_eq_tsum_halfOpenCube` + periodicity of the folded
  inner integral, `∑'ₙ χ(y+n)² ≤ ∑'ₙ 1_{B̄}(y+n) ≤ 343 = 7³`, the finite
  lattice-cover count).
- `iB_bound : IB v ≤ ENNReal.ofReal cbConst · ‖v‖²_{L²(Q)}`,
  `cbConst = 686·Jval.toReal`.  `‖(χ(x+h)-χ x)•v x‖² = (χ(x+h)-χ x)²‖v x‖²`;
  `(χ(x+h)-χ x)² ≤ min(L²‖h‖²,1)·(1_{B̄}(x)+1_{B̄}(x+h))` (`cutoffLip` via
  `Convex.norm_image_sub_le_of_norm_fderiv_le`, and the `≤1` range bound, plus
  support localization); tiling `∫⁻_{support} ‖v‖² ≤ 343·‖v‖²_{L²(Q)}`; and
  `Jval = ∫⁻ h, min(ofReal(L²‖h‖²),1)·fractionalRadialKernel (1/2) h < ⊤`
  (`Jval_lt_top`, near part exponent `2 < 3` via `integrableOn_ball_of_norm_le_rpow`,
  far part exponent `4 > 3` via `finite_integral_one_add_norm`, mirroring
  `cFrac_lt_top`).

Probe `research/T12/probes/cutoff_gagliardo_closes.lean` closes the target
verbatim and instantiates it on a genuine nonzero smooth mean-zero periodic
witness `probeMZ = meanZeroPartT (x ↦ cos(2π x₀)·e₀)` (mean-zero for free from
`T10.mean_decomposition`), so the theorem is non-vacuous.

## Development notes / failed approaches (for the ledger)

- **`whnf` blow-up (backbone)**: `rw [lintegral_add_left …]` / `lintegral_const_mul`
  directly on `∫⁻ x, 2 * gA v h x` times out at 200k and 400k heartbeats —
  `gA` unfolds `cutoff = (cutoffBump : ContDiffBump)`, whose coercion body is
  enormous under `whnf`.  Fix: prove the iterated-lintegral linearity as an
  abstract lemma `lintegral_two_add_two (f g)` over *variable* `f, g`, and give
  every intermediate measurability `have` its beta-reduced type explicitly
  (`have hfx : Measurable (fun x => f h x) := …`) so the `rw` matches
  syntactically.
- **`a² ≤ b² → a ≤ b` in ℝ≥0∞**: `pow_le_pow_iff_left` needs
  `MulLeftStrictMono`, which ℝ≥0∞ lacks; use
  `(ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ)<2)).mp` after `ENNReal.rpow_two`.
- **pin-specific renames**: monotone-mul is `mul_le_mul_right h a : a*b ≤ a*c`
  (multiply left) and `mul_le_mul_left h a : b*a ≤ c*a`; `Measurable (fun x =>
  (h,x))` is `measurable_prodMk_left`; `mul_le_mul_right'` gone (use `mul_le_mul'`
  with `le_rfl`); `norm_image_sub_le_of_norm_fderiv_le` is in `namespace Convex`;
  `Set.indicator_of_not_mem → Set.indicator_of_notMem`;
  `EuclideanSpace.single_apply → PiLp.single_apply`;
  `fun x : Space => x 0` is `ContDiff` by `contDiff_piLp_apply 2`.
- A double `rw [mul_zero, mul_zero]` fails (`rw` rewrites all syntactically
  identical `Ecut h * 0` at once) — use one `mul_zero`.
- `simpa [chiBall]` over-normalizes `ENNReal.ofReal (‖v x‖^2)` into `‖v x‖ₑ^2`,
  breaking a `set M` match — use `simp only [add_zero] at h0; exact h0`.

The two kernel bounds were developed in parallel by prover subagents (lattice
counting `lattice_count_le`, kernel finiteness `Jval_lt_top`) and integrated;
the lead re-verified the whole module compiles warning-free, all axioms clean,
and folded the two bounds + final theorem into the single module.
