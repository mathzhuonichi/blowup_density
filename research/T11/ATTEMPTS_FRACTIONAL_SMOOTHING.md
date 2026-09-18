# Lane 329 (T11 U9d1b) — attempts, dead ends, exact errors

Scope: the `σ = 3/2` smoothing estimate for the coefficient heat semigroup.
No named input, no `sorry`/`axiom`, no edits to existing modules; one new module
`formalization/NSFormalization/Section3/T11/FractionalSmoothing.lean`, one probe,
one conformance file. Work confined to this worktree; no fetch/merge/rebase/push.

## 0. Prior-art grep (before claiming anything is "not in the tree")

`grep -rn` over `formalization/NSFormalization/Paper1/Periodic*.lean`,
`formalization/NSFormalization/Section3/`, `Section4/{A01,A02,A04,D01}` and
`vendor/HeliCorgi/Formal/` for `3 / 4`, `3/4`, `rpow … heatSymbol`, `smoothing`:
no fractional (non-integer) heat gain exists anywhere. What exists is

* `Paper1/PeriodicHeatMultiplier.lean:…` `sqrt_weight_mul_heatSymbol_le` — the
  `σ = 1` symbol bound `W(k)^{1/2} e^{-νtΛ(k)} ≤ (1 + 1/(νt))^{1/2}`;
* `Section3/T11/LocalExistenceProbe.lean` `torusMultiplier`,
  `torusMultiplier_norm_le`, `torusHeat`, `torusHeatSmoothing`,
  `torusHeatSmoothing_norm_le` (σ = 1), `torusSmoothingKernel`;
* `Section3/T11/LocalExistence.lean` `torusMultiplierCLM`, `torusHeatCLM`,
  `torusHeatCLM_continuous`, `torusSmoothingCLM`, `torusSmoothingKernel_le`,
  `torusSmoothingKernel_integrable`;
* `vendor/HeliCorgi/Formal/EndpointSafeTwoSpaceDuhamel.lean:429-438` — the
  abstract `smoothingKernel` fields the new kernel is shaped for.

All new declarations reuse `torusMultiplier`/`torusMultiplierCLM` rather than
re-deriving the `lp`/`PiLp` bookkeeping. Every instance in this shared namespace
carries an explicit name (`fracSmoothingNormedGroup`, `fracSmoothingNormedSpace`,
`fracProbeNormedGroup`, `fracProbeNormedSpace`) — `logs/LESSONS.md` 2026-09-17.

## 1. Three routes to the symbol bound; which one was taken

Target: `W(k)^{3/4} e^{-a x} ≤ C_T a^{-3/4}` with `a = νt ∈ (0, νT]`,
`x = Λ(k) = 4π²|k|² ≥ 0`, `W(k) = 1 + x`.

* **Route A (the brief's literal hint).** `a^{3/4}(1+x)^{3/4}e^{-ax} ≤
  a^{3/4}e^{-ax} + (ax)^{3/4}e^{-ax} ≤ (νT)^{3/4} + (3/4)^{3/4}e^{-3/4}`.
  Needs subadditivity `(u+v)^p ≤ u^p + v^p` for `0 ≤ p ≤ 1`. **Rejected**: the
  Mathlib lemma for `ℝ` at this pin was not located by `grep -rn
  "rpow_add_rpow_le_rpow"` (only `ℝ≥0`/`ℝ≥0∞` families surfaced), so it would
  have to be proved by hand, and it *loses* constant sharpness.
* **Route B (recycle the σ = 1 bound).** `W^{3/4}e^{-ax} =
  (W^{1/2}e^{-2ax/3})^{3/2} ≤ (1 + 3/(2a))^{3/4}`, i.e. `C_T = (νT + 3/2)^{3/4}`,
  using `sqrt_weight_mul_heatSymbol_le` at time `2t/3`. **Rejected**: strictly
  worse constant (`3/2` instead of `(3/4)e^{-1} ≈ 0.2759`) and an extra
  `Real.rpow` composition `( ·^{1/2})^{3/2}` to justify.
* **Route A′ (taken).** Keep the two terms combined:
  `a^{3/4}W^{3/4}e^{-ax} = (a(1+x)e^{-4ax/3})^{3/4}` and
  `a(1+x)e^{-4ax/3} = a e^{-4ax/3} + a x e^{-4ax/3} ≤ a + (3/4)e^{-1} ≤ νT + (3/4)e^{-1}`,
  the second summand straight from `Real.mul_exp_neg_le_exp_neg_one (4ax/3)`.
  Gives `torusFracConst ν T = (νT + (3/4)e^{-1})^{3/4}`, no subadditivity, and
  its `x`-only part is exactly the brief's `(3/4)^{3/4}e^{-3/4}`. The brief's
  scalar maximization is still proved on its own, as
  `rpow_three_quarters_mul_exp_neg_le`, and instantiated in the probe §7.

## 2. Two routes to strong continuity; which one was taken

* **Rejected:** repeat the `continuous_tsum` + summable-square-majorant argument
  of `LocalExistence.lean` `torus_scalarHeat_continuous`, with the `t`-uniform
  majorant `C_T (ν t₀/2)^{-3/4}` valid on `[t₀/2, T]`. Correct but ≈60 lines and
  a second copy of the same analysis.
* **Taken:** factor the symbol through the semigroup,
  `torusFracSymbol ν t k = torusHeatSymbol ν (t-δ) k * torusFracSymbol ν δ k`
  (`torusFracSymbol_sub`), with `δ = t₀/2`. On `Icc (t₀/2) T` the path is then
  literally `torusHeatCLM hν.le (Real.toNNReal (t - δ)) A'` for the fixed datum
  `A' = torusHeatSmoothingFrac s hν … A`, so the existing joint continuity
  `torusHeatCLM_continuous` supplies everything. `ContinuousWithinAt` is then
  transported from `Icc (t₀/2) T` to `Ioc 0 T` with
  `ContinuousWithinAt.mono_of_mem_nhdsWithin` and
  `inter_mem_nhdsWithin (Ioc 0 T) (Ioi_mem_nhds …)`.
  Note `torusHeat s … = torusHeat r … ` definitionally (the order index of
  `PeriodicSobolev` is a phantom), which is why the order-3 heat CLM applies
  verbatim at order `s + 3/2`.

The path has to be a *total* function of `t` for `ContinuousOn` to be stated, so
`torusFracPath` uses `dite` on `0 < t ∧ t ≤ T` and is `0` off the window; only
values on `Ioc 0 T` enter `ContinuousOn`, and `torusFracPath_eq` identifies them
with `torusHeatSmoothingCLM_frac`. The consumer-facing form
`torusHeatSmoothingCLM_frac_continuousOn` quantifies over an arbitrary path `u`
agreeing with the CLM on the window, so no consumer has to use `torusFracPath`.

## 3. Exact errors hit and their fixes

1. Final rearrangement of the symbol bound, attempted with `nlinarith [hinv]`:
   ```
   error: linarith failed to find a contradiction
   a✝ : (1 + x) ^ (3 / 4) * Real.exp (-(a * x)) <
        a ^ (3 / 4) * ((1 + x) ^ (3 / 4) * Real.exp (-(a * x))) * a ^ (-(3 / 4))
   ⊢ False
   ```
   `nlinarith` will not use `a^{3/4} a^{-3/4} = 1` to cancel two rpow atoms.
   Fixed by an explicit `ring`-proved reassociation followed by `rw [hrw, hinv, mul_one]`.
2. ```
   error: Unknown identifier `intervalIntegrable_rpow'`
   ```
   The lemma is `intervalIntegral.intervalIntegrable_rpow'` (as already used in
   `LocalExistence.lean` `torusSmoothingKernel_integrable`).
3. ```
   error: Invalid field `congr_fun`: The environment does not contain `And.congr_fun`
     Integrable.const_mul hbase (ν ^ (-(3 / 4)))
   ```
   `IntegrableOn` unfolds to the `Integrable` structure, so dot notation resolves
   into `And`. Fixed by naming the intermediate `IntegrableOn` and calling
   `IntegrableOn.congr_fun` in prefix position.
4. ```
   error: Type mismatch: IntervalIntegrable.comp_sub_left hb t enorm_ne_top
     has type IntervalIntegrable (fun x => torusFracKernel ν (t - x)) volume t 0
     but is expected to have type … volume 0 t
   ```
   `comp_sub_left` produces `(c-a)..(c-b)`, i.e. `t..0` here. Fixed with `.symm`.
5. Deprecations at this pin (`leanprover/lean4:v4.34.0-rc2`): `dif_pos` →
   `dite_eq_left`, `if_pos` → `ite_eq_left`, `if_neg` → `ite_eq_right`.
   Both files are now warning-free.
6. Probe audit: `probeFrequency` and `probeFrequency_ne_neg` print
   `depends on axioms: [propext]` — a strict subset of the three standard axioms;
   the `#guard_msgs` docstrings record the exact observed output.

## 4. Non-vacuity — why the constant mode is not enough on its own

At `k = 0` the symbol is `1` (`torusFracSymbol_zero`), so the zero mode is fixed
(`torusHeatSmoothingFrac_constant`, and the module's non-vacuity `example`).
That witnesses non-triviality but not decay. The probe therefore also builds a
genuine **single lattice mode**: a single `k₀ ≠ 0` is *not* in
`realPeriodicSubmodule` (it violates `A i (-k) = star (A i k)`), so the smallest
honest object is the conjugate pair `{k₀, -k₀}` with a real amplitude —
`singleMode`, at `k₀ = (1,0,0)`. `singleMode_frac_apply` computes its image
coefficient as `torusFracSymbol ν t k₀ · c`, nonzero for `c ≠ 0` because the
symbol is strictly positive.

## 5. Residual / out of scope (no named input was introduced)

Everything delivered is unconditional. The following were **not** attempted and
are not claimed:

* `TorusHalfStepInput` (`Section3/T11/Persistence.lean`) is *not* discharged.
  This lane supplies only the linear half of it — the `H^r → H^{r+3/2}` gain with
  an integrable kernel. The missing half is the endpoint Duhamel argument on
  `Ico 0 T` together with a real-order bilinear bound `H^r × H^r → H^{r-1}`
  (lane 317's `torusScalarConvectionLp_norm_le` is order-3 only). The brief for
  this lane says so explicitly, as does `Persistence.lean`'s docstring
  ("a fractional multiplier estimate alone does not discharge it").
* No sharpness/lower bound for `torusFracConst` is proved; it is an upper bound.
* No statement identifies the heat image with an `IsPeriodicDatum` of a physical
  field: `torusHeatSmoothingFrac … A` is the reweighting of the *heat image* of
  `A`, which is a datum of `e^{νtΔ}z`, not of `z`; producing the physical field
  is `U9d`'s Fourier-inversion problem (lane 318, partial).
* The kernel mass `4 t^{1/4} ν^{-3/4}` is proved as an `intervalIntegral`
  identity; it is not yet wired into any `EndpointSafeTwoSpace*` contract field.
