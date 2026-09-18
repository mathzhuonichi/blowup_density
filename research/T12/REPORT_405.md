# REPORT_405 — T12 U6 `gradientLambdaCriticalL3` (Opus; transcribed by lead from the agent message, report-file guard)

Lane 405 is complete: the U6 target closed verbatim, no residual, no named input.

## 1. What was proved

The `gradientLambdaCriticalL3` field of `MeanZeroSobolevCalculusAPI` (probe `research/T12/probes/api_on_canonical.lean:170-175`), **verbatim** — same binders, same order, same two sides:

```lean
theorem gradientLambdaCriticalL3 :
    ∀ (v Lv : SpatialField), SmoothPeriodicT v →
      MemPeriodicHomogeneous (3 / 2) v → IsPeriodicLambda v Lv →
        periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
          ENNReal.ofReal CcriticalThreeHalves *
            periodicHomogeneousENorm (3 / 2) v
```

Constant: `def CcriticalThreeHalves : ℝ := 4 * CcriticalHalf` (three gradient columns plus the `Λ` term, each paid for by U4's order-`1/2` constant `CcriticalHalf = criticalL3Const * cutoffGagliardoConst * (gapConst (1/2) + 1)`), with `CcriticalThreeHalves_pos`.

Route, exactly as planned in `T12_SPLIT.md` U6: (a) `‖∇v‖_{L³} ≤ ∑_j ‖∂_j v‖_{L³}` via a torus copy of `A05.eLpNorm_le_sum_of_norm_le` plus `A05.norm_toLp_le_sum`; (b) lane 396's `velocityCriticalL3_smooth` applied to each `∂_j v` and to `Lv`; (c) the two Fourier order shifts, both resting on one weight identity `homogeneousDatumWeight (3/2) k = homogeneousDatumWeight (1/2) k · 2π|k|`.

**Answer to the brief's open question about `Lv`**: `IsPeriodicLambda v Lv` *does* pin `Lv` — its first conjunct is `SmoothPeriodicT Lv` (`MeanZeroCalculus.lean:96`). So there is no a.e.-representative problem, no extra premise is needed, and lane 401's general `velocityCriticalL3` is **not** required. The `Lv` half is delivered unconditionally, not under an added hypothesis. Moreover the `Λ` order shift is an equality in disguise: the order-`1/2` homogeneous datum of `Lv` *is*, term for term, the order-`3/2` datum of `v`, so its constant is `1`. The `∂_j` shift has multiplier `2πi k_j/(2π|k|)` of modulus `|k_j|/|k| ≤ 1`, also constant `1`.

The `MemPeriodicHomogeneous (3/2) v` hypothesis is carried but never used (bound as `_hmem`): U4 already handles the `⊤` right-hand side and both order shifts are unconditional. That is a strengthening, not a weakening.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/405-T12-U6-gradient-lambda-l3/formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean` (407 lines, 24 declarations) — new module, namespace `NSFormalization.Section3.T12`. Contents: §0 `cxReweight` + `cxReweight_apply/_norm_le/_enorm_le/_real` (bounded **complex** Fourier multiplier on the datum carrier); §1 `homogeneousDatumWeight_three_halves`, `abs_derivSymbol_le_sqrt`, `norm_periodicDerivativeSymbol`, `derivShiftReal`, `derivShift`, `norm_derivShift_le`, `derivShift_conj`; §2 `contDiff_dirDeriv`, `isPeriodicSpatial_dirDeriv`, `isMeanZeroT_dirDeriv`; §3 `isMeanZeroT_lambda`; §4 `homogeneousENorm_half_dirDeriv_le`, `homogeneousENorm_half_lambda_le`; §5 `eLpNorm_torus_le_sum_of_norm_le`, `periodicLpENorm_gradientTensor_le_sum`; §6 the constant and the target.
- `/data_8T/ping/blowup_density/.claude/worktrees/405-T12-U6-gradient-lambda-l3/research/T12/probes/gradient_lambda_l3_closes.lean` — closes the API field by `exact gradientLambdaCriticalL3`, plus the order shifts, the column bound, the weight identity, and non-vacuity: the field instantiated at the nonzero smooth mean-zero witness `probeMZ = meanZeroPartT (x ↦ cos(2πx₀)·e₀)` with the `Lv` produced by `lambda_exists`.
- `/data_8T/ping/blowup_density/.claude/worktrees/405-T12-U6-gradient-lambda-l3/research/T12/axioms_u6.lean` — audits all 24 declarations.
- `/data_8T/ping/blowup_density/.claude/worktrees/405-T12-U6-gradient-lambda-l3/research/T12/ATTEMPTS_U6.md`, U6 status block in `.../research/T12/T12_SPLIT.md`, one new top line in `.../logs/LESSONS.md`.
- No existing module was edited; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`. Commit `cb052e90` on `erenup/405-T12-U6-gradient-lambda-l3`; nothing pushed, merged or rebased.

## 3. Gaps

None for U6 — the field is closed as stated for every `v`, `Lv` satisfying its three hypotheses. U4's own density residual (general `MemPeriodicHomogeneous (1/2)` without smoothness, `ATTEMPTS_U4.md`) does not propagate here, because U6 consumes U4 only on the smooth fields `∂_j v` and `Lv`.

Failed approaches, with the exact error text (all in `ATTEMPTS_U6.md`):

- **`SpectralGap.reweightDatum` for the derivative shift** — it takes `w : PeriodicFrequency → ℝ`, and must, since `reweightDatum_real` needs `w (-k) = w k`; the symbol `2πi k_j` is imaginary and odd. Factoring as `I • reweightDatum r A` fails too (`I • A ∉ realPeriodicSubmodule`). Hence `cxReweight` with condition `w (-k) = star (w k)`.
- **`rw [← Real.rpow_add]` inside `homogeneousDatumWeight`**: `error: Tactic 'rewrite' failed: Did not find an occurrence of the pattern periodicAngularFrequencySq k ^ ?y * periodicAngularFrequencySq k ^ ?z in the target expression (periodicAngularFrequencySq k).rpow (3 / 2 / 2) = (periodicAngularFrequencySq k).rpow (1 / 2 / 2) * periodicAngularFrequencySq k ^ (1 / 2)` — the definition uses the explicit function `Real.rpow`, the lemmas use `^`; fixed with a `show` restating the goal in `^` form.
- **`derivShift` as a quotient**: `error(lean.unknownIdentifier): Unknown identifier 'star_div''` — redefined as `(derivShiftReal k : ℂ) * periodicDerivativeSymbol j k`, closed by `star_mul` + `Complex.conj_ofReal`.
- **`mul_le_mul_left'`**: `error(lean.unknownIdentifier): Unknown identifier 'mul_le_mul_left''` (the renamed-lemma pitfall already in `LESSONS.md`); replaced by `gcongr` at both sites.
- **`exact_mod_cast` straight onto `IsMeanZeroT`**: `error: mod_cast has type (meanT Lv).ofLp i = 0 but is expected to have type (meanT Lv).ofLp i = ↑0` — both mean-zero lemmas now prove `∀ i, meanT w i = 0` first, then `ext i; exact hall i`.
- Two `push_cast; field_simp; ring` blocks had `error: No goals to be solved` at the trailing `ring` (`field_simp` had already closed them); removed.

## 4. Commands run and results

All from the worktree, after `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section3.T12.CriticalL3 NSFormalization.Section3.T10.ForcePaths` → `Build completed successfully (10039 jobs).`
- `lake build NSFormalization.Section3.T12.GradientLambdaL3` → `✔ [10040/10040] Built NSFormalization.Section3.T12.GradientLambdaL3 (3.2s)`, `Build completed successfully (10040 jobs).` (0 errors; the only warnings in the run come from the pre-existing `NSFormalization/Source/FractionalRealization.lean` linter note, not from this module)
- `lake env lean ../formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean` → 0 lines of output
- `lake env lean ../research/T12/probes/gradient_lambda_l3_closes.lean` → 0 lines of output
- `lake env lean ../research/T12/axioms_u6.lean` → 24 declarations, every one `depends on axioms: [propext, Classical.choice, Quot.sound]`
- `make check` → `rc=0` (`check_formalization_plan`, `check_contracts`, `test_contract_policy` 13 tests OK, `check_work_queue`: `45 work items: ownership, contract registration and task cards consistent.`)
- `grep -nE "sorry|admit|axiom|native_decide|maxHeartbeats"` on the module and probe → no matches
- `git commit` → `cb052e90 [405-T12] U6: gradientLambdaCriticalL3 verbatim ...`, 6 files changed, 726 insertions.

Per the brief's fallback, this message is the report in place of `research/T12/REPORT_405.md` (my harness forbids writing report files); the durable substance is in `research/T12/ATTEMPTS_U6.md` and the U6 status block of `research/T12/T12_SPLIT.md`.
