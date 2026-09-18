# REPORT_413 — T20 U7 critical trilinear estimate (Opus; transcribed by lead from the agent message, report-file guard)

Lane 413 is complete and committed. Report below.

---

## 1. What was proved

The **T20 U7 mean-zero critical trilinear estimate** — the analytic core of `prop:critical`, `paper/sections/03-torus.tex:425-431`:

> `|⟪(v·∇)v, Λv⟫| ≤ ‖v‖₃ ‖∇v‖₃ ‖Λv‖₃ ≤ C₀ y z²`

Closed completely. No named input, no placeholder, no residual.

Main theorem, exact statement (`NSFormalization.Section3.T20.criticalTrilinear`):

```lean
theorem criticalTrilinear (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v)
    (hthree : MemPeriodicHomogeneous (3 / 2) v)
    (hL : IsPeriodicLambda v Lv) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      criticalTrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        (periodicHomogeneousENorm (3 / 2) v).toReal ^ 2
```

**Exact constant**: `criticalTrilinearConst := CcriticalHalf * CcriticalThreeHalves ^ 2`, equal to `16 * CcriticalHalf ^ 3` (`criticalTrilinearConst_eq`), positive (`criticalTrilinearConst_pos`). This is the `C₀` that U13 installs into `CriticalRegularityTAPI`.

**The two finiteness premises are not new obligations for U8.** They are the fourth conjuncts of `MemPeriodicHomogeneous (1/2) v` and `(3/2) v`, which `reductionRegular` (U1) already hands over as its third and fourth conjuncts. The `ℝ≥0∞` form `criticalTrilinear_enorm` needs no finiteness hypothesis at all.

**U7 is no longer blocked on T12**, and U8 is unblocked: both inputs (lane 401's `velocityCriticalL3`, lane 405's `gradientLambdaCriticalL3`) are in the tree and used as registered black boxes.

## 2. What exists in Lean now

`/data_8T/ping/blowup_density/.claude/worktrees/413-T20-U7-critical-trilinear/formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean` (327 lines, 13 declarations):

- §0 `aestronglyMeasurable_torusLift`, `continuous_gradientTensor`
- §1 `lintegral_enorm_mul_three_le_torus` — three-factor Hölder (3,3,3) on `periodicTorusMeasure`
- §2 `enorm_inner_advection_le`, `criticalAdvectionHolderT` (the `≤ ‖v‖₃‖∇v‖₃‖Λv‖₃` line)
- §3 `criticalTrilinearConst`, `_eq`, `_pos`, `criticalTrilinear_enorm`, `criticalTrilinear`
- §4 U8 bridges: `periodicPairing_eq_integral_torusLift_inner` (`rfl`), `criticalTrilinear_pairing`, `advection_eq_slice` (`rfl`)

Supporting files (all absolute paths under the same worktree root):
- `research/T20/probes/critical_trilinear_closes.lean`
- `research/T20/axioms_u7.lean`
- `research/T20/ATTEMPTS_U7.md`
- `research/T20/T20_SPLIT.md` (U7 status line added)
- `logs/LESSONS.md` (one line added)

**Route deviation from the brief, deliberate**: the brief's step (2) said to transfer the Haar integral to the cube via `HaarCube` and Hölder against `volume.restrict fundamentalCube`. The cube is not needed — `periodicLpENorm p w` is *definitionally* `eLpNorm (torusLift w) p periodicTorusMeasure`, and the estimated quantity is already a Haar integral, so the Hölder runs directly on the torus. The cube route would add two transports that cancel (`integral_torusLift` lands in `cubeIntegral`, an integral over `Coords` rather than `Space`, needing a further `toSpace` change of variables, then all three `L³` norms moved back). Same constant, strictly more work.

**Shape check for U8 passes with no bridging step.** The probe's §3 type-checks the full U8 slice statement — left side in `meanFreeEquation`'s `advection (meanFreeVelocity g u) t x` spelling, right side in `criticalY`/`criticalZ` — discharged by a bare `criticalTrilinear_pairing` application. `criticalY v t` is definitionally `periodicHomogeneousENorm (1/2) (fun x ↦ v (t,x))` and `advection u t x` is definitionally the slice advection, so both bridges are `rfl`.

## 3. Gaps

**No mathematical gap in the delivered lemma** — the estimate is closed end to end.

**One failed step, recorded.** First draft wrote the constant algebra as `← ENNReal.ofReal_mul (by positivity)`:

```
error: NSFormalization/Section3/T20/CriticalTrilinear.lean:257:31:
  failed to prove positivity/nonnegativity/nonzeroness
```

`CcriticalHalf` and `CcriticalThreeHalves` are opaque `def`s with no `positivity` extension, so the tactic cannot see through them even with `*_pos` lemmas adjacent. Fixed with explicit `mul_nonneg CcriticalHalf_pos.le CcriticalThreeHalves_pos.le` plus a `← mul_assoc` before splitting the `ofReal`. That was the only failure in the lane.

**Three things could not be reused and had to be re-proved** (details in `ATTEMPTS_U7.md`): `R43/Trilinear.lean:176 lintegral_enorm_mul_three_le` is hard-wired to `volume` on `Space` (its Mathlib engine `ENNReal.lintegral_prod_norm_pow_le` *is* measure-general, so the proof was repeated for `periodicTorusMeasure`); `Paper1.measurable_torusLift` is `ℂ`-only and `T10.memLp_torusLift_vector` is `SpatialField`-only, while the middle Hölder factor lands in `WithLp 2 (Fin 3 → Space)`, and `HaarCube`'s `torusChart`/`measurableEmbedding_torusChart` are `private` — hence the two-line general helper in §0; continuity of `gradientTensor` has no exported lemma.

**A constant tightening is available and was deliberately not taken.** Using lane 405's registered field as a black box costs the full `4·CcriticalHalf` for each of the two order-`3/2` factors, since the field bounds the *sum* `‖∇v‖₃ + ‖Λv‖₃`. Lane 405's internal `hgrad`/`hlam` would give `C₀ = 3·CcriticalHalf³` instead of `16·CcriticalHalf³` (a factor 16/3), and all four ingredients are exported, so U7 could re-derive them in ~20 lines. I did not, because it duplicates the interior of a registered field in a second module — exactly the drift the reuse rule exists to prevent — and nothing downstream evaluates `C₀` numerically (U13 needs only `0 < C₀` and `c < 1/(4C₀)`, and any positive `C₀` admits a positive `c`). If a future unit ever needs a numerically smaller threshold, the cheap fix is to export `hgrad`/`hlam` from `T12/GradientLambdaL3.lean` as a V2 and shrink the constant here. This is written up in `ATTEMPTS_U7.md`.

## 4. Commands run and results

| Command (from `verification/`, after `. scripts/lean-env.sh`) | Result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.CriticalTrilinear` | `Build completed successfully (10646 jobs).` exit 0, **0 errors, 0 warnings on the new module** |
| `lake env lean ../formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean` | **no output** (clean) |
| `lake env lean ../research/T20/probes/critical_trilinear_closes.lean` | **no output** (clean) — every `example` closed, including the nonzero witness and the U8 slice shape check |
| `lake env lean ../research/T20/axioms_u7.lean` | all **13** declarations print exactly `[propext, Classical.choice, Quot.sound]` |
| `make check` (from root) | exit 0 — plan check, contract check, 13 contract-policy tests `OK`, `45 work items: ownership, contract registration and task cards consistent.` |
| `lake -d verification test` | exit 0 — all registered contracts `checked; standard logical axioms only` |
| `grep -nE "sorry\|admit\|axiom\|native_decide\|maxHeartbeats"` on module + probe | only the docstring sentence asserting their absence |

Earlier failing build (before the fix): `✖ Building NSFormalization.Section3.T20.CriticalTrilinear` with the single `positivity` error quoted in §3.

Commit `e5511d97` on `erenup/413-T20-U7-critical-trilinear`, 6 files (1 new module, 3 new research files, 2 record files modified). Working tree clean. Not pushed, not merged, not rebased; no existing module edited.
