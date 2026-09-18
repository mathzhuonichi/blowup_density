# T12 U6 — `gradientLambdaCriticalL3`, attempts and route (lane 405)

Module `formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean`.
Probe `research/T12/probes/gradient_lambda_l3_closes.lean`, axioms
`research/T12/axioms_u6.lean`.

## What closed

The API field **verbatim**, no named input, no extra hypothesis:

```
theorem gradientLambdaCriticalL3 :
    ∀ (v Lv : SpatialField), SmoothPeriodicT v →
      MemPeriodicHomogeneous (3 / 2) v → IsPeriodicLambda v Lv →
        periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
          ENNReal.ofReal CcriticalThreeHalves * periodicHomogeneousENorm (3 / 2) v
```

with `CcriticalThreeHalves = 4 * CcriticalHalf` (three gradient columns plus the
`Λ` term, each paid for by U4's order-`1/2` constant) and
`CcriticalThreeHalves_pos`.  `MemPeriodicHomogeneous (3 / 2) v` is carried but not
needed: the proof never has to exclude the infinite right-hand side, because U4
already handles it and the two order-shift steps are unconditional.

## Route (exactly `T12_SPLIT.md` U6)

1. `periodicLpENorm 3 (gradientTensor v) ≤ ∑_j periodicLpENorm 3 (∂_j v)`
   (`periodicLpENorm_gradientTensor_le_sum`): pointwise
   `A05.norm_toLp_le_sum` (the Frobenius `l² ≤ l¹` bound on the three columns,
   `gradientTensor v x j = A05.dirDeriv j v x` is `rfl`) fed into a torus copy of
   `A05.eLpNorm_le_sum_of_norm_le` (`eLpNorm_torus_le_sum_of_norm_le`; the A05
   version is stated for `volume` on `Space` only), the measurability side
   conditions from `T10.memLp_torusLift_vector`.
2. Each column and `Lv` is smooth periodic mean-zero, so U4's
   `velocityCriticalL3_smooth` applies at order `1/2`:
   * smooth: `(hs.fderiv_right (by simp)).clm_apply contDiff_const`;
   * periodic: `NavierStokes.PeriodicUniqueness.spatial_partial_periodic`
     (`dirDeriv` and `spatialPartial` are the same term);
   * mean-zero (`isMeanZeroT_dirDeriv`): the zero-mode coefficient is
     `periodicDerivativeSymbol j 0 * ĉ(0) = 0`
     (`T10.periodicFourierCoeff_gradientTensor`), and
     `T10.periodicFourierCoeff_zero_eq_mean_component` turns that into
     `meanT (∂_j v) i = 0`;
   * for `Lv`, `IsPeriodicLambda v Lv` **does** pin it: its first conjunct is
     `SmoothPeriodicT Lv` (`MeanZeroCalculus.lean:96`), so no a.e.-representative
     issue arises and lane 401's general `velocityCriticalL3` is *not* needed;
     mean-zero (`isMeanZeroT_lambda`) is the zero mode of the graph equation,
     `sqrt (periodicAngularFrequencySq 0) = 0`.
3. Order shift, both halves through the single weight identity
   `homogeneousDatumWeight (3/2) k = homogeneousDatumWeight (1/2) k · 2π|k|`
   (`homogeneousDatumWeight_three_halves`, `Real.rpow_add` at `1/4 + 1/2 = 3/4`):
   * `Λ` (`homogeneousENorm_half_lambda_le`): the order-`1/2` homogeneous datum of
     `Lv` **is** the order-`3/2` datum `A` of `v`, term for term, so the bound is
     `iInf_le_of_le ⟨A.1, hA⟩ le_rfl` — an equality in disguise, constant `1`.
   * `∂_j` (`homogeneousENorm_half_dirDeriv_le`): the datum of `∂_j v` is
     `derivShift j` applied to `A`, with
     `derivShift j k = (2π|k|)⁻¹ · 2πi k_j`, `‖derivShift j k‖ = |k_j|/|k| ≤ 1`
     (`norm_derivShift_le`, from `abs_derivSymbol_le_sqrt`), so the reweighting is
     a contraction and again the constant is `1`.
4. Assembly: `3·(C·H) + C·H = 4C·H`, `ENNReal.ofReal_mul` for the constant.

## Attempts that failed, and why

* **`SpectralGap.reweightDatum` for the derivative shift.** It only carries a
  **real** multiplier (`w : PeriodicFrequency → ℝ`), and it must, because
  `reweightDatum_real` needs `w (-k) = w k` to preserve
  `realPeriodicSubmodule`.  The derivative symbol `2πi k_j` is imaginary and
  *odd*, so no real `w` reproduces it.  Factoring as `I • (reweightDatum r A)`
  does not help either: `I • A ∉ realPeriodicSubmodule`, so the conjugate-symmetry
  obligation has to be discharged by hand anyway.  §0 therefore repeats the
  construction for a bounded **complex** multiplier (`cxReweight`,
  `cxReweight_norm_le`, `cxReweight_enorm_le`, `cxReweight_real` with the
  conjugate condition `w (-k) = star (w k)`).
* **`rw [← Real.rpow_add]` inside `homogeneousDatumWeight`.** `homogeneousDatumWeight`
  is spelled with the explicit function `Real.rpow x (s/2)`
  (`T10/PeriodicData.lean:167`), while `Real.rpow_add` and `Real.sqrt_eq_rpow` are
  stated with the `^` notation; the two terms are defeq but not syntactically
  equal, so the rewrite reports "did not find an occurrence".  Fixed by a `show`
  that restates the goal in `^` form after `simp only [homogeneousDatumWeight, hk,
  ↓reduceIte]`.
* **`derivShift` defined as a quotient `symbol / (2π|k| : ℂ)`.** The conjugation
  lemma then needs `star (a / b) = star a / star b`; `star_div'` does not exist at
  this pin.  Redefined as `(derivShiftReal k : ℂ) * periodicDerivativeSymbol j k`
  with the real factor `(2π|k|)⁻¹`, after which `star_mul` +
  `Complex.conj_ofReal` closes it in three lines.
* **`mul_le_mul_left'`** is not the name of the monotone-multiplication lemma at
  this pin (already recorded in `logs/LESSONS.md` for lane 354/U4): `gcongr` is
  used at both places instead.
* **`exact_mod_cast` straight onto `IsMeanZeroT`.** After `ext i` the goal reads
  `(meanT w).ofLp i = WithLp.ofLp 0 i`, and `norm_cast` will not bridge that to the
  complex zero-mode identity.  Both mean-zero lemmas therefore prove
  `∀ i, meanT w i = 0` first and finish with `ext i; exact hall i`.

## No residual

Nothing in U6 is left open: the field is closed as stated, for every `v`, `Lv`
satisfying its three hypotheses.  U6 consumes U4 only through
`velocityCriticalL3_smooth`, and only on the smooth fields `∂_j v` and `Lv`, so
U4's own general-`MemPeriodicHomogeneous` density residual
(`research/T12/ATTEMPTS_U4.md`) does not propagate here.

All 24 declarations audit to `[propext, Classical.choice, Quot.sound]`.
