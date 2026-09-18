# Lane 344 (T13 `constant_pos_finite` / `endpoint_zero` / `endpoint_one`) — attempts

Module: `formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean`.
No named input; all three targets are proved outright.

## 1. `constant_pos_finite` — routes considered

`cFrac s = ∫⁻ h, ofReal ‖e^{i h₀} − 1‖² · (ofReal ‖h‖)^{−(3+2s)}` is an
`ℝ≥0∞`-valued integral over `Space = EuclideanSpace ℝ (Fin 3)`.

### 1a. Route rejected: dyadic annuli
Cover `ℝ³ \ {0}` by `{2^k < ‖h‖ ≤ 2^{k+1}}`, bound each piece with
`Measure.addHaar_ball` and sum the two-sided geometric series over `ℤ`.
Rejected before writing Lean: the `ℤ`-indexed `ENNReal.tsum` split into the
positive and negative halves is far more Lean work than the radial reduction,
and it needs `lintegral_iUnion_le` plus a countable cover argument.

### 1b. Route rejected: layer cake
`MeasureTheory.lintegral_eq_lintegral_meas_lt` turns the integral into
`∫₀^∞ volume {G > t} dt`; the distribution function of
`min(‖h‖²,4)·‖h‖^{−3−2s}` has three regimes and no closed form that Mathlib
already knows. Rejected.

### 1c. Route taken: radial majorant + `integrable_fun_norm_addHaar`
Mathlib has **no** `lintegral` version of the radial reduction — only the
Bochner ones in `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
(`integrable_fun_norm_addHaar`, `integral_fun_norm_addHaar`) and the ball-only
`integrableOn_ball_of_norm_le_rpow` in
`Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean`.  Neither covers the
far field on its own (`integrableOn_ball_of_norm_le_rpow` is a ball statement;
there is no `Ioi`-analogue for `‖x‖^{-α}` at infinity).

So the integrand is dominated by the **radial** majorant
`cFracRadial s y = min (y²) 4 * y ^ (-(3+2s))` (the paper's own two-regime
bound), `integrable_fun_norm_addHaar` reduces integrability of
`h ↦ cFracRadial s ‖h‖` to `IntegrableOn (fun y ↦ y^2 • cFracRadial s y) (Ioi 0)`,
and the 1-D statement splits as `Ioi 0 = Ioo 0 1 ∪ Ici 1`:
* `Ioo 0 1`: `y² · cFracRadial s y = y^{1−2s}` exactly (`min` resolves to `y²`),
  integrable iff `−1 < 1−2s`, i.e. `s < 1`
  (`intervalIntegral.integrableOn_Ioo_rpow_iff`).
* `Ici 1`: dominated by `4·y^{−1−2s}`, integrable iff `−1−2s < −1`, i.e. `0 < s`
  (`integrableOn_Ioi_rpow_iff` + `Ioi_ae_eq_Ici`).
Finally `Integrable.hasFiniteIntegral` + `Real.enorm_eq_ofReal` transports the
Bochner finiteness to the `lintegral`.

### Numerator bounds — dead ends and the fix
First attempt was to prove `‖e^{it}−1‖² = 2 − 2 cos t` by hand from
`Complex.exp_mul_I` and `Complex.normSq_apply`. Abandoned once
`grep` found that Mathlib already has the exact evaluation and the sharp bound:
* `Complex.norm_exp_I_mul_ofReal_sub_one : ‖exp (I*x) − 1‖ = ‖2 * Real.sin (x/2)‖`
* `Real.norm_exp_I_mul_ofReal_sub_one_le : ‖exp (I*x) − 1‖ ≤ ‖x‖`
(both in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean` and
`Mathlib/Analysis/Complex/Trigonometric.lean`). These give all three facts used
here: `≤ t²`, `≤ 4`, and `> 0` on `0 < t < 1` (via
`Real.sin_pos_of_pos_of_lt_pi` and `Real.pi_gt_three`).

### Positivity
`ENNReal.lintegral_eq_zero_iff'` + the observation that the integrand is
**nowhere** zero on the open slab `{h | 0 < h 0 < 1}`: the kernel factor is
never `0` (`ENNReal.rpow_eq_zero_iff` — `ofReal ‖h‖ ≠ ⊤` and the exponent is
negative, so even the singular value `⊤` at `h = 0` is nonzero), and the
numerator is positive there. `IsOpen.measure_pos` on a nonempty open set closes
it. An earlier plan to lower-bound the integral on a concrete ball
(`c = (3/2,0,0)`, `ρ = 1/4`) was dropped: it needs a numeric lower bound on
`sin` on that ball, which the support argument avoids entirely.

## 2. Endpoints — the geometric core

Both endpoints reduce to the **single-copy** lemma
`periodize_eq_of_mem_cube`: if `tsupport f ⊆ ball c r` and
`closure (ball c r) ⊆ interior fundamentalCube`, then for every
`x ∈ fundamentalCube` and every `n ≠ 0`, `f (x − latticeVector n) = 0`.

The proof needs `interior fundamentalCube ⊆ (0,1)³`, i.e. that the interior is
**strict** in each coordinate; with only `interior ⊆ fundamentalCube` the
argument gives `n i ∈ {−1,0,1}` and stalls. `interior_subset_fundamentalCubeInterior`
supplies it by the usual `ε`-argument with `EuclideanSpace.single i (ε/2)`.
`interior_fundamentalCube : interior fundamentalCube = (0,1)³` is then recorded
as an equality (the `⊇` half is `interior_maximal`).

`tsum_eq_single` at this toolchain needs the summation filter explicitly:
`tsum_eq_single (L := SummationFilter.unconditional PeriodicFrequency) 0 …`
(pattern copied from `vendor/.../PeriodicLocalization.lean:250`).

### `endpoint_one` — the boundary
`fderiv` is local, so the cube equality must be upgraded to a *neighbourhood*
equality, which only holds on `interior fundamentalCube`.

* Attempt A (rejected): show `periodize f = f` on an open `δ`-neighbourhood of
  the *closed* cube, using `δ = dist (closure (ball c r)) ((0,1)³)ᶜ > 0`. Correct
  but needs a compactness/separation argument in Lean.
* Attempt B (taken): the leftover `fundamentalCube \ interior fundamentalCube`
  is contained in `frontier fundamentalCube`, which is null because
  `fundamentalCube` is convex — `Convex.addHaar_frontier`. `Measure.restrict_apply'`
  (only `MeasurableSet fundamentalCube` needed, not measurability of the bad
  set) turns this into the required `∀ᵐ` statement.

Off the cube the integrand vanishes because `x ∉ tsupport f` gives
`f =ᶠ[𝓝 x] 0` (`notMem_tsupport_iff_eventuallyEq`) hence `fderiv ℝ f x = 0`;
`Set.indicator_eq_self` + `lintegral_indicator` then convert
`∫⁻ … in fundamentalCube` into `∫⁻ …` over all of `Space`.

## 3. Error texts actually hit (and their fixes)

* `Failed to rewrite using equation theorems for cFracRadial` — `rw [cFracRadial]`
  does not unfold a plain `def`; use `simp only [cFracRadial]` / `unfold`.
* `failed to prove positivity/nonnegativity` from `positivity` on
  `0 ≤ y ^ 2 * cFracRadial s y` — `positivity` cannot see through the `def`;
  unfold first and give the product of nonnegativity facts by hand.
* `Did not find an occurrence of the pattern y ^ 2 * y ^ ?a` — natural powers
  and `Real.rpow` do not mix under `rw`; the helper
  `npow_mul_rpow_of_pos : y^n * y^a = y^((n:ℝ)+a)` plus
  `show y^2 * y^2 = y^(4:ℕ) by ring` is what actually works.
* `Did not find an occurrence of the pattern (PiLp.single ?p ?i ?a).ofLp ?j`
  after a `show x i - _ = _` step — the `show` rewrites the goal into
  `WithLp.equiv … .toFun` form and `PiLp.single_apply` no longer matches; plain
  `simp` on the unmassaged goal proves
  `(x ± EuclideanSpace.single i a) i = x i ± a`.
* `Did not find an occurrence of the pattern fderiv ?m (Function.const ?m ?c)` —
  `fderiv_const` does not match `fderiv ℝ (fun x => 0) x`; `simp` does.
* `‖EuclideanSpace.single i a‖`: `EuclideanSpace.norm_single` is deprecated and
  `PiLp.norm_single 2 _ i a` times out at `whnf` (200000 heartbeats) because the
  `β` family has to be unified; `simp` gives `= |a|` instantly.
* `2⁻¹ < 1` left open by `simp` on the nonemptiness witness — `norm_num` after
  `rw [PiLp.single_apply]`.

## 4. What is *not* proved here

`wholeSpace_identity`, `torus_identity`, `localization` (lanes 345/346).
Nothing in this module assumes them; the probe's
`localizationAPI_of_remaining_fields` takes them as explicit hypotheses only to
type-check the three proved fields against the real record.
