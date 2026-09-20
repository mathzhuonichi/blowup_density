# T20 U7 — attempts (lane 413, 2026-09-18)

Target: the mean-zero critical trilinear estimate `|⟪(v·∇)v,Λv⟫| ≤ C₀ y z²`
(`paper/sections/03-torus.tex:425-431`), the lemma `criticalEnergy` (U8) consumes.
Delivered in `formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean`.
Closed completely; no named input, no residual.

## Route actually taken (and the one deviation from the brief)

The brief's route (2) was: transfer the Haar integral to the cube with the
`T12/HaarCube.lean` lemmas, then run a `lintegral_enorm_mul_three_le`-style
Hölder against `volume.restrict fundamentalCube`.  **The cube is not needed.**
`periodicLpENorm p w` is *definitionally* `eLpNorm (torusLift w) p periodicTorusMeasure`
(`T12.periodicLpENorm_eq_eLpNorm_torusLift`, proved by `rfl`), and the quantity
being estimated is itself a Haar integral over `PeriodicTorus`.  So the whole
Hölder step runs directly against `periodicTorusMeasure` and the chart never
appears.  Going through the cube would have cost two extra transports that
cancel: `Paper1.integral_torusLift` moves the Bochner integral to `cubeIntegral`
(an integral over `Coords`, not `Space` — an extra `toSpace` change of variables),
and `eLpNorm_torusLift_eq_restrict` would then have to move all three `L³` norms
back. Same constant, strictly more work.

## What could not be reused, and why

- **`Section4/R43/Trilinear.lean:176 lintegral_enorm_mul_three_le`** — the exact
  three-factor `3,3,3` Hölder needed, but its measure is hard-wired to `volume`
  on `Space` (`{f : Space → E} … ∂volume`), so it does not apply on the torus.
  Its engine, Mathlib's `ENNReal.lintegral_prod_norm_pow_le`, *is*
  measure-general (`{μ : Measure α}`), so §1 of the new module repeats the R43
  proof verbatim with `periodicTorusMeasure` in place of `volume`.  Editing R43
  to generalize the measure was not an option (no edits to existing modules, and
  `Section4/*` is registered-contract territory).
- **`Paper1.measurable_torusLift`** (`Paper1/TorusCube.lean:54`) is stated only
  for `{f : Space → ℂ}`; **`T10.memLp_torusLift_vector`**
  (`T10/ForcePaths.lean:18`) only for `SpatialField`.  The middle Hölder factor
  is `gradientTensor v`, valued in `WithLp 2 (Fin 3 → Space)`, so neither
  applies.  `T12/HaarCube.lean` has exactly the right fact
  (`measurableEmbedding_torusChart`) but both it and `torusChart` are `private`
  there and cannot be imported.  §0 therefore re-proves the two-line chart
  measurability and derives a target-general
  `aestronglyMeasurable_torusLift : Continuous w → AEStronglyMeasurable (torusLift w) …`
  via `Continuous.comp_aestronglyMeasurable`.
- Continuity of `gradientTensor v` has no exported lemma either; §0 mirrors the
  `show`-then-`PiLp.continuous_toLp` pattern of `R43/Trilinear.lean:236` over
  `T12.contDiff_dirDeriv`.

## Failed tactic steps (one only)

`ENNReal.ofReal_mul` needs the left factor's nonnegativity, and the first draft
wrote it as `← ENNReal.ofReal_mul (by positivity)` for
`0 ≤ CcriticalHalf * CcriticalThreeHalves`:

```
error: NSFormalization/Section3/T20/CriticalTrilinear.lean:257:31:
  failed to prove positivity/nonnegativity/nonzeroness
```

`CcriticalHalf` (`T12/CriticalL3.lean:134`) and `CcriticalThreeHalves`
(`T12/GradientLambdaL3.lean:362`) are opaque `def`s with no `positivity`
extension, so the tactic cannot see through them even though `*_pos` lemmas
exist right next to them.  Replaced by explicit
`mul_nonneg CcriticalHalf_pos.le CcriticalThreeHalves_pos.le`, with the
association fixed by `← mul_assoc` *before* splitting the `ofReal`.  That was the
only failure in the lane; everything else compiled first try.

## The constant, and the tightening that is available but not taken

Taken: `criticalTrilinearConst = CcriticalHalf * CcriticalThreeHalves ^ 2`, i.e.
`16 * CcriticalHalf ^ 3` (since `CcriticalThreeHalves = 4 * CcriticalHalf`).
This is what falls out of using lane 405's **registered U6 field**
`gradientLambdaCriticalL3` as a black box: it bounds the *sum*
`‖∇v‖₃ + ‖Λv‖₃ ≤ CcriticalThreeHalves · z`, and each summand is then bounded by
the sum, so each of the two order-`3/2` factors costs the full `4C`.

A factor `16/3` is recoverable: lane 405's proof internally has
`‖∇v‖₃ ≤ 3·CcriticalHalf·z` (`hgrad`) and `‖Λv‖₃ ≤ CcriticalHalf·z` (`hlam`),
which would give `C₀ = 3 · CcriticalHalf ^ 3`.  Those two `have`s are not
exported, but all four of their ingredients are
(`periodicLpENorm_gradientTensor_le_sum`, `velocityCriticalL3_smooth`,
`homogeneousENorm_half_dirDeriv_le`, `homogeneousENorm_half_lambda_le`), so U7
could re-derive them in ~20 lines.  **Not done on purpose:** it duplicates the
interior of a registered field in a second module (drift risk of exactly the kind
the reuse rule exists to prevent), and nothing downstream evaluates `C₀`
numerically — U13 only needs `0 < C₀` and `c < 1/(4C₀)`, and any positive `C₀`
admits a positive `c`.  If a future unit ever needs a numerically smaller
threshold, the cheap fix is to export `hgrad`/`hlam` from
`T12/GradientLambdaL3.lean` as a V2 and shrink `criticalTrilinearConst` here.

## Statement-fidelity notes for U8

- The estimate is stated in **three** interchangeable spellings, all proved:
  the raw Haar integral of the lifted inner product, the `periodicPairing` form
  (`criticalTrilinear_pairing`), and the `ℝ≥0∞` form without `.toReal`
  (`criticalTrilinear_enorm`, which needs no finiteness hypothesis at all).
  `periodicPairing_eq_integral_torusLift_inner` is `rfl`.
- The two `.toReal` finiteness hypotheses are *not* extra obligations for U8:
  they are the fourth conjuncts of `MemPeriodicHomogeneous (1/2) v` and
  `MemPeriodicHomogeneous (3/2) v`, which `reductionRegular` (U1) hands over
  verbatim as its third and fourth conjuncts.
- `advection_eq_slice : advection u t x = advection (lift (fun y ↦ u (t,y))) 0 x`
  is `rfl`, so `meanFreeEquation`'s space-time advection needs no conversion.
  Likewise `criticalY v t` / `criticalZ v t` are definitionally
  `periodicHomogeneousENorm (1/2 resp. 3/2) (fun x ↦ v (t,x))`; §3 of the probe
  type-checks the whole U8 slice statement with no bridging step.
