# U2 attempts — lane 309

## Search and successful routes

Read CLAUDE, split §0–§4, reconciliation §0–§3, implementation candidates, and first 40 LESSONS lines. Both FlowConversion and FourierCalculus are present. Ran `grep -rnE 'periodicSobolevENorm|smoothPeriodicWeightedFourierLp|FiniteH2Energy|integrable_torusLift'` over `Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, and `vendor/HeliCorgi/Formal/`: 44 matches, local log `tmp/309-search.log`. No absent-lemma claim is needed.

1. Componentwise `smoothPeriodicWeightedFourierLp` constructs the vector; `periodicFourierCoeff_real_neg` and even weights establish real-submodule membership. `continuous_torusLift`, compact-torus integrability, real projection, and `Integrable.of_eval_piLp` supply Haar integrability.
2. Canonical `datum_unique` evaluates the infimum at any datum. `PiLp.norm_eq_of_L2`, `lp.norm_eq_tsum_rpow`, and `norm_periodicWeightedCoeff_sq` identify its norm with the Paper1 vector Bessel norm. This works for all data, beyond smooth fields.
3. `w.sobolev m` gives a continuous path and hence continuous extended norm and real squared H² profile on `Ico 0 S`. Restricting to `Ioo` supplies measurability.
4. Norm identification gives equality of nonnegative lintegrals on `Ioo`. `hasFiniteIntegral_iff_ofReal` and measurable profile give integrability; `restrict_Ioo_eq_restrict_Ioc` handles the terminal singleton. Both directions follow without assuming finite energy.

## Exact resolved errors

- `Application type mismatch: The argument ContDiff.comp (ContinuousLinearMap.contDiff ?m.63) hs has type ContDiff ℝ ∞ (⇑?m.63 ∘ z) but is expected to have type ContDiff ℝ ∞ fun x => (z x).1 i`.
  Fix: explicit `(𝕜 := ℝ)` on `EuclideanSpace.proj`.
- `Invalid field `integrable_of_isCompact`: The environment does not contain `Continuous.integrable_of_isCompact``; next spelling: `Invalid field `integrable`: The environment does not contain `Continuous.integrable``.
  Fix: `continuousOn.integrableOn_compact ... isCompact_univ`, simplifying restriction to univ.
- `Tactic `rewrite` failed: Did not find an occurrence of the pattern periodicSobolevENorm ↑2 fun x => w.velocity (t, x)`.
  Fix: explicitly type the datum certificate at real order `2` before rewriting the certificate originally at natural `2` cast to ℝ.
- `Tactic `rewrite` failed: Did not find an occurrence of the pattern HasFiniteIntegral (fun t => ?m.222 t ^ 2) ?m.209`.
  Fix: type the nonnegativity certificate as `0 ≤ h2SquaredProfile (toFlow w) t` before applying `hasFiniteIntegral_iff_ofReal`.
- Documentation insertion initially failed with `AssertionError` because the expected line-break anchor was wrong. No file was changed by that attempt; retried with the exact existing substring and verified the inserted status line.

## Residual input

None. Ten unconditional theorems with their displayed ordinary datum/smoothness/solution parameters. Non-vacuity is checked for every constant field and explicitly for `coordinateVector 0`. Every theorem has exactly the three standard axioms. No instance was added.
