# Lane 462-T15-U14b-q2-negative-order — T15 U14b: `forceConvergence` for `q = 2` (the rescaled force tends to `0` in `L²_t H^s_x` for every `s < −1/2`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/462-T15-U14b-q2-negative-order` (git branch `erenup/462-T15-U14b-q2-negative-order`, = lane 458's branch + `origin/erenup/integration-section3`).
Lane 458 delivered the `q = 1` half of U14 (`Section3/T15/Convergence.lean`: `forceConvergence_one` for all `s < 1/2`, plus `forceSobolevENormT_mono_order`, `persistenceDown_norm_le_one`) and proved the `q = 2` route in the
original brief wrong: `alphaT 2 2 = −1/2`, so the order-0 comparison `forceSobolevENormT 2 s F_ε ≤ forceSobolevENormT 2 0 F_ε = ofReal (ε^{−1/2})·‖F‖` **diverges** — read `research/T15/ATTEMPTS_U14.md` ("The `q = 2` sign
obstruction", "Exact canonical mismatch and residual") and `research/T15/REPORT_458.md`. Also read `CLAUDE.md`, `research/T15/T15_SPLIT.md` §0 + U14, the canonical field `forceConvergence` (`Section3/T15/Scaling.lean:447-452`),
`paper/sections/03-torus.tex:133-158`, `Section3/T10/PeriodicData.lean` (`periodicFrequencyWeight k = 1 + 4π²Σ kᵢ²`, `IsPeriodicDatum`, `periodicSobolevENorm = ⨅ ‖A‖ₑ`, `forceSobolevENormT q s f = ⨅ eLpNorm G q` over paths),
`Section3/T10/FourierCalculus.lean:33 norm_periodicFourierCoeff_le` (`‖ĉ_k(f)‖ ≤ ∫ ‖torusLift f‖`), `Section3/T15/SobolevBound.lean` (lane 456: `chartForce`, `periodize_chartForce`, `chartForce_fourierNorm`, `packetEndpoint`,
how the order-`s` path of the periodized packet is built and bounded slice by slice), `Section3/T15/Mixed.lean` (`torusLift_periodizedScaledForce`, `eLpNorm_torusLift_eq_volume`, `packetMixedScaling` = the `L²_tL²_x` scaling
`mixedLebesgueENormT 2 2 F_ε = ofReal (ε^{alphaT 2 2})·‖F‖`), `Section3/T15/ParsevalZero.lean` (order-0 norm = `L²`), `Section3/T18/SobolevRate.lean:139 persistenceDown_norm_le`, `Section3/T11/ConvolutionBoundReal.lean:100`
(`Summable (W^(−r))` for `r ≥ 3`, via `Paper1.PeriodicInverseWeightSummable.summable_inverse_weight_cube`), Mathlib `NNReal.inner_le_Lp_mul_Lq_tsum` / `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg` (`Mathlib/Analysis/MeanInequalities.lean:705-760`),
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T15.Convergence`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## The mathematics (sharp scaling, then a route that only needs tools already in the tree)
With `F_ε(t,x) = ε^{−3}F((t−T)/ε², (x−x₀)/ε)` periodized (single copy in the cell), the slice at `t = T + ε²τ` is `g_τ := F_ε(t,·)` and for `−3/2 < s < 0`: `‖g_τ‖_{H^s(T³)} ≲ ε^{−3/2−s}‖F(τ)‖`, hence
`‖F_ε‖_{L²_tH^s_x} ≲ ε^{−3/2−s}·ε = ε^{−1/2−s} → 0` iff `s < −1/2 = criticalOrder 2`. Two ingredients give this without any new lattice-counting:
- **(I) an `ε`-free negative-order bound.** For `s₁ < −3/2`: `‖g‖²_{H^{s₁}} = Σᵢ Σ_k W_k^{s₁}|ĉ_{i,k}|² ≤ (Σ_k W_k^{s₁})·Σᵢ (∫_{T³}|gᵢ|)²` by `norm_periodicFourierCoeff_le`, and the single-copy `L¹` slice is scale-invariant:
  `∫_{T³}|F_ε(t,·)| = ∫_{ℝ³}|F(τ,·)|` (mirror `packetMixedScaling`'s change of variables at exponent 1). So `‖F_ε(t)‖_{H^{s₁}} ≤ C_{s₁}‖F(τ)‖_{L¹}` with `C_{s₁}² = Σ_k W_k^{s₁}`. **Summability for `s₁ ∈ (−∞, −3/2)`** is needed
  (the tree has it only for `s₁ ≤ −3`; prove `Summable (fun k : PeriodicFrequency ↦ periodicFrequencyWeight k ^ s₁)` for `s₁ < −3/2` via `1 + Σ kᵢ² ≥ Πᵢ (1 + kᵢ²)^{1/3}` so `W_k^{s₁} ≤ (4π²)^{…}Πᵢ (1+kᵢ²)^{s₁/3}`, a product of three
  one-dimensional summable series (`s₁/3 < −1/2`; `Real.summable_one_div_int_rpow`/`summable_int_rpow`-type lemmas, `summable_prod`/`Summable.mul_of_nonneg` over `Fin 3 → ℤ`), or by dyadic comparison with the `r = 3` case —
  record which). If only `s₁ ≤ −3` is reachable in time, the interpolation below still closes **`s < −1`** and the residual is exactly the strip `−1 ≤ s < −1/2`: deliver that honestly.
- **(II) interpolation between orders `0` and `s₁`.** For `s = (1−θ)·s₁ + θ·0`, `θ ∈ (0,1)`: `Σ_k W_k^{s}|c_k|² = Σ_k (W_k^{0}|c_k|²)^θ (W_k^{s₁}|c_k|²)^{1−θ} ≤ (Σ_k |c_k|²)^θ (Σ_k W_k^{s₁}|c_k|²)^{1−θ}` (Hölder for `tsum`,
  exponents `1/θ`, `1/(1−θ)`). With `‖g_τ‖_{H^0} = ‖g_τ‖_{L²} = ε^{−3/2}‖F(τ)‖_{L²}` (ParsevalZero + `packetMixedScaling`-type slice scaling) and (I): `‖F_ε(t)‖_{H^s} ≤ (ε^{−3/2}‖F(τ)‖_{L²})^θ (C_{s₁}‖F(τ)‖_{L¹})^{1−θ}`; after the
  `L²_t` change of variables (`dt = ε²dτ`, factor `ε`): `‖F_ε‖_{L²_tH^s_x} ≤ C ε^{1 − 3θ/2}` with `θ = 1 − s/s₁`. Given `s < −1/2`, choose `s₁ ∈ (−3/2 − η, −3/2)` close enough to `−3/2` that `1 − 3θ/2 > 0` (this holds iff
  `s < s₁/3`, i.e. iff `s₁ > 3s`; with `3s < −3/2` such an `s₁ > −3/2`-close value exists) — then `ε^{1−3θ/2} → 0` along `𝓝[>] 0`. For `s ≤ s₁` use `forceSobolevENormT_mono_order` and (I) directly (`ε^{1}` → 0).
  The datum/path plumbing (`IsPeriodicSobolevPath`, `AEStronglyMeasurable`, `Ioc 0 place.ε₀` vs `𝓝[>] 0` via `Filter.Eventually`/`Ioc_mem_nhdsGT`, squeeze `tendsto_of_tendsto_of_tendsto_of_le_of_le`) is exactly as in
  `Convergence.lean` / `SobolevBound.lean` — reuse, do not re-derive.

## Goal
New module `formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean` (namespace `NSFormalization.Section3.T15`): `theorem forceConvergence_two … : ∀ s : ℝ, s < criticalOrder ((2 : ℝ≥0∞).toReal) → Tendsto (fun ε ↦ forceSobolevENormT 2 s
(periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0)` over the same raw hypotheses as `forceConvergence_one` (`hf : ContDiff ℝ ∞ f`, `hc : CompactPositiveTimeSupport f`, `place`), and `theorem forceConvergence` with the
canonical field's type (`∀ q, (q = 1 ∨ q = 2) → ∀ s < criticalOrder q.toReal, …`, combining 458's `forceConvergence_one` and the new theorem; probe by `exact` against `Section3/T15/Scaling.lean:447-452`). Deliverables: the module,
`research/T15/probes/convergence_two_closes.lean` (field by `exact` + the nonzero packet instance), `research/T15/axioms_u14b.lean`, `research/T15/ATTEMPTS_U14b.md`, U14b status line in `T15_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.ConvergenceTwo` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_462.md`.
