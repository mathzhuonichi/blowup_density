# B02 units 3 & 4 — attempts log (`low_frequency_weight`, `angular_fourier_sup_bound`)

Lane 036. Module: `formalization/NSFormalization/Section4/B02/LowFrequency.lean`.
Conformance: `research/B02/axioms_u34.lean`.

Three spec fields discharged (all rated S), all `sorry`-free, axioms
`[propext, Classical.choice, Quot.sound]`:

- `lowFrequencyIntegrable` (Spec.lean:370)
- `lowFrequencyIntegral` (Spec.lean:379, exact value `4π` at `s=-1`)
- `fourierSupBound` (Spec.lean:397, vector form)

## What worked

### `lowFrequencyIntegrable`
One-liner reusing `NSFormalization.Paper3.homogeneous_low_frequency_integrable`
(`Paper3/SobolevWeights.lean:54`, the source COMPARISON named `SW:54`) at the
constant profile `φ ≡ (1:ℂ)`, `C = 1`. That lemma yields
`IntegrableOn (fun ξ => ‖ξ‖^(2s) * ‖φ ξ‖^2) (ball 0 1)`; `simpa` collapses
`‖(1:ℂ)‖^2 = 1`. No need to touch `integrableOn_ball_of_norm_le_rpow` directly.

### `lowFrequencyIntegral = 4π`
Radial reduction via `MeasureTheory.integral_fun_norm_addHaar` (`MHS:296`):
`∫ ξ, f ‖ξ‖ = dim • volume.real(ball 0 1) • ∫ y in Ioi 0, y^(dim-1) • f y`.
Steps:
1. Rewrite the ball integral `∫ ξ in ball 0 1, ‖ξ‖^(2·(-1))` as `∫ ξ, g ‖ξ‖`
   with `g = (Iio 1).indicator (·^(2·(-1)))`, via `integral_indicator` +
   pointwise `by_cases` on `ξ ∈ ball 0 1` (`Set.indicator_of_mem` /
   `Set.indicator_of_notMem`, membership through `Metric.mem_ball`,
   `dist_zero_right`).
2. `Module.finrank ℝ Space = 3` by `simp [Space, finrank_euclideanSpace]`.
3. `volume.real (ball 0 1) = π·4/3` from `EuclideanSpace.volume_ball_fin_three`
   + `ENNReal.toReal_ofReal`.
4. Inner integral `∫ y in Ioi 0, y²·g y = 1`: push `y²` inside the indicator
   (`by_cases`), `setIntegral_indicator measurableSet_Iio`,
   `Set.Ioi_inter_Iio` (= `Ioo 0 1`), then on `Ioo 0 1` the integrand collapses
   `y^(2:ℕ)·y^(2·(-1):ℝ) = 1` via `Real.rpow_natCast`, `Real.rpow_add`,
   `Real.rpow_zero`; `∫_{Ioo 0 1} 1 = 1` by `simp`.
5. `3 • (π·4/3) • 1 = 4π` by `simp [smul_eq_mul, nsmul_eq_mul]; push_cast; ring`.

### `fourierSupBound` (vector form — the hard one)
Form the `EuclideanSpace ℂ (Fin 3)`-valued integrand
`F x = e^{-i⟪x,ξ⟫} • (complexify (k x))` and apply
`MeasureTheory.norm_integral_le_integral_norm`:
- `angularFourier_eq_integral` (`FC:27`) gives the honest integral
  `angularFourier (k_i) ξ = (2π)^{-3/2} • ∫ e^{-i⟪x,ξ⟫}·k_i(x)`.
- coordinate of the vector integral = scalar integral, via
  `(EuclideanSpace.proj i).integral_comp_comm hF_int` (`simpa` turns
  `proj i (∫F)` into `(∫F) i`).
- `‖F x‖ = ‖k x‖`: `EuclideanSpace.norm_eq`, phase unimodular
  (`Complex.norm_exp_ofReal_mul_I`), `Complex.norm_real`.
- amplitude pulled out of the sum of squares (`norm_smul`, `sq_abs`), then
  `Real.sqrt_mul`/`Real.sqrt_sq` and `← EuclideanSpace.norm_eq (∫F)` collapse
  `√(∑ ‖(∫F) i‖²)` to `‖∫F‖`.
- `(2π)^{-3/2} = frequencyUnit^{-3/2}` closed by `unfold frequencyUnit; norm_num`
  (exponents `-3/2` and `-(3)/2` are the same term `(-3)/2`).

The vector triangle inequality is essential: the ℓ²≤ℓ¹ shortcut
`√(∑‖a_i‖²) ≤ ∑‖a_i‖ ≤ ∑∫|k_i| = ∫‖k‖_{ℓ¹}` bounds by the ℓ¹ integral, which is
≥ the ℓ² integral in the target — wrong direction, exactly the "spurious factor 3"
the spec docstring warns about.

## What failed / pitfalls (and the fixes)

1. **`positivity` cannot prove `0 ≤ frequencyUnit^(-3/2)`** — `frequencyUnit` is an
   opaque `def` it will not unfold. Fix: `Real.rpow_nonneg frequencyUnit_pos.le _`.
   (For `0 ≤ (2·π)^…` `positivity` is fine — `π` is known positive.)

2. **No `aestronglyMeasurable_pi_iff` in this Mathlib** (v4.34.0-rc2). First tried
   `rw [aestronglyMeasurable_pi_iff]` → unknown identifier.

3. **`isDefEq` timeout (≥1M heartbeats) when composing through `EuclideanSpace.equiv.symm`.**
   Building `F` as `equiv.symm (fun i => e·↑(k x i))` and proving aesm via
   `Continuous.comp_aestronglyMeasurable` with a `Prod.mk`ed argument made the
   unifier unfold `equiv.symm` / `PiLp` / `Prod.fst/snd` and time out.
   Fix: define `F x = e^{-i⟪x,ξ⟫} • G x` with `G x = equiv.symm (complexify (k x))`,
   and get aesm as `he.aestronglyMeasurable.smul hG_aesm` where
   `hG_aesm = equiv.symm.continuous.comp_aestronglyMeasurable (hCplx.comp_aestronglyMeasurable hInt.aestronglyMeasurable)`
   and `hCplx : Continuous (complexify) = continuous_pi (fun i => ofReal ∘ proj i)`.
   No `Prod`, no annotated re-matching through `equiv.symm` — compiles instantly.

4. **`apply Continuous.smul` fails to unify** `Continuous (?f • ?g)` with a lambda
   `Continuous (fun a => c a • v a)`. Fix: build `h1 h2` and `exact h1.smul h2`
   (term mode; the `f • g` vs `fun a => f a • g a` mismatch is only a defeq the
   `exact` accepts).

5. **`Set.indicator_of_not_mem` renamed** to `Set.indicator_of_notMem`.

6. **Beta-redex blocks `rw`**: after `setIntegral_congr_fun`/`sum_congr` the
   integrand appears as `(fun y => …) y`; `rw [← Real.rpow_natCast …]` cannot find
   `y ^ 2`. Fix: give the pointwise equality as a standalone `Set.EqOn … := by intro y hy; show …` where `show` beta-reduces first.

## Exact Mathlib / repo names used

- `NSFormalization.Paper3.homogeneous_low_frequency_integrable` (SobolevWeights.lean:54)
- `MeasureTheory.integral_fun_norm_addHaar`, `EuclideanSpace.volume_ball_fin_three`
- `MeasureTheory.integral_indicator`, `MeasureTheory.setIntegral_indicator`,
  `MeasureTheory.setIntegral_congr_fun`, `Set.Ioi_inter_Iio`, `Real.volume_Ioo`
- `Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_zero`, `Real.rpow_nonneg`,
  `Real.sqrt_mul`, `Real.sqrt_sq`, `sq_abs`
- `NSFormalization.Source.angularFourier(_eq_integral)`, `frequencyUnit(_pos)`
- `EuclideanSpace.equiv`, `EuclideanSpace.proj`, `EuclideanSpace.norm_eq`,
  `ContinuousLinearMap.integral_comp_comm`, `MeasureTheory.norm_integral_le_integral_norm`
- `Complex.norm_exp_ofReal_mul_I`, `Complex.norm_real`, `Complex.continuous_ofReal`,
  `Complex.continuous_exp`, `AEStronglyMeasurable.smul`,
  `Continuous.comp_aestronglyMeasurable`, `MemLp`/`memLp_one_iff_integrable`,
  `Integrable.mono'`, `Integrable.norm`

## Commands

From worktree, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake run from `verification/`:
- `lake build NSFormalization.Section4.B02.LowFrequency` → `Build completed successfully`.
- `lake env lean ../research/B02/axioms_u34.lean` → 3× `depends on axioms:
  [propext, Classical.choice, Quot.sound]`.
