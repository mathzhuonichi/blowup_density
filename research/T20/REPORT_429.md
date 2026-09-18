# REPORT_429 — T20 U10a H¹ trilinear estimate (Opus; transcribed by lead from the agent message, report-file guard)

Lane 429 is complete. Full report:

---

## 1. What was proved

T20 unit **U10a**, the mean-zero `H¹` trilinear estimate of `paper/sections/03-torus.tex:467-477` — the nonlinear term U10b's `hOneEnergy` field must absorb. **Closed completely: no named input, no placeholder, no residual, no `sorry`/`admit`/`axiom`/`native_decide`, no `maxHeartbeats` override.**

The target theorem, stated in exactly the U10b slice spelling (`laplacianSqT` of `CriticalRegularity.lean:98`):

```lean
theorem h1Trilinear (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        laplacianSqT v
```

**Constant:** `def h1TrilinearConst : ℝ := CcriticalHalf * Csix`, with `h1TrilinearConst_pos : 0 < h1TrilinearConst`. Expanded, `Csix = 343 * A05.gradientL6Const * leibnizConst * (1 + 2 * hTwoConst)` (lane 400) and `CcriticalHalf` is lane 396/401's order-`1/2` critical `L³` constant. This is the `C₁` U10b/U13 install.

Route, exactly as briefed: pointwise Cauchy–Schwarz (lane 413's `enorm_inner_advection_le`, already stated for an arbitrary second factor, at `Lv := laplacian v`) → three-factor Hölder with exponents `(3,6,2)`, `1/3+1/6+1/2 = 1`, taken directly against normalized Haar measure via Mathlib's `ENNReal.lintegral_prod_norm_pow_le` → `T12.velocityCriticalL3` (`‖v‖₃ ≤ CcriticalHalf·y`, lane 401) and `T12.gradientLSix` (`‖∇v‖₆ ≤ Csix·‖Δv‖₂`, lane 400).

I checked the brief's optional Fourier step first, as instructed: **`‖∇(∂ⱼv)‖₂ ≤ ‖Δv‖₂` (`:475-477`) is not needed.** `gradientLSix` is stated as `periodicLpENorm 6 (gradientTensor v) ≤ ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)` — literally the spelling the Hölder step produces — and the per-derivative comparison is internal to lane 400's `periodicLpENorm_gradientTensor_le_laplacian` (`GradientLSix.lean:167`).

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/429-T20-U10a-h1-trilinear/formalization/NSFormalization/Section3/T20/H1Trilinear.lean` — 16 declarations, namespace `NSFormalization.Section3.T20`:
  - §0 `measurable_torusChartH1`, `aestronglyMeasurable_torusLiftH1`, `continuous_gradientTensorH1`, `enorm_inner_advection_leH1` (lane 413 helpers, see gap §3);
  - §1 `lintegral_enorm_mul_three_le_torus_three_six_two` — the new `(3,6,2)` torus Hölder;
  - §2 `h1AdvectionHolderT` — `|⟪(v·∇)v,Δv⟫| ≤ ‖v‖₃‖∇v‖₆‖Δv‖₂`, in `ℝ≥0∞`, no integrability premise;
  - §3 `h1TrilinearConst`, `h1TrilinearConst_pos`, `h1Trilinear_enorm` (`ℝ≥0∞` form, **no finiteness hypothesis**), `periodicLpENorm_two_laplacian_ne_top`, `h1Trilinear_toReal` (`‖Δv‖₂²` written out), `h1Trilinear` (the `laplacianSqT` form above);
  - §4 `periodicPairing_eq_integral_torusLift_innerH1` (`rfl`), `h1Trilinear_pairing`, `advection_eq_sliceH1` (`rfl`), `h1Trilinear_slice` (the `criticalY` / `laplacianSqT` time-slice form U10b applies).
- `/data_8T/ping/blowup_density/.claude/worktrees/429-T20-U10a-h1-trilinear/research/T20/probes/h1_trilinear_closes.lean` — non-vacuity at the genuine nonzero smooth mean-zero witness `probeMZ = meanZeroPartT (x ↦ cos(2πx₀)·e₀)` (with `probeMZ ≠ 0` proved and `‖Δ probeMZ‖₂ ≠ ⊤`, so the `.toReal` is not a junk zero), plus the U10b shape check at `fun x ↦ meanFreeVelocity g u (t, x)`.
- `/data_8T/ping/blowup_density/.claude/worktrees/429-T20-U10a-h1-trilinear/research/T20/axioms_u10a.lean` — all 16 declarations.
- `/data_8T/ping/blowup_density/.claude/worktrees/429-T20-U10a-h1-trilinear/research/T20/ATTEMPTS_U10A.md`, plus a U10a status block in `research/T20/T20_SPLIT.md` and one line at the top of `logs/LESSONS.md`.

Commit `1f01ab12` on `erenup/429-T20-U10a-h1-trilinear`. Nothing pushed, merged or rebased; no existing module edited.

## 3. Gaps

**No mathematical gap.** One repository-level blocker, which is a lead item, not a lane item:

`NSFormalization.Section3.T12.contDiff_dirDeriv` is declared **twice** — `formalization/NSFormalization/Section3/T12/GradientLSix.lean:184` (lane 400, general target `{w : Space → F}`) and `formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean:210` (lane 405, specialized to `{v : SpatialField}`). Same one-line proof; the lane-400 version subsumes the other. My first attempt imported `T20.CriticalTrilinear` (to reuse lane 413's machinery as briefed) together with `T12.GradientLSix`, and got:

```
error: NSFormalization/Section3/T20/H1Trilinear.lean:1:0: import
NSFormalization.Section3.T12.GradientLSix failed, environment already contains
'NSFormalization.Section3.T12.contDiff_dirDeriv'
from NSFormalization.Section3.T12.GradientLambdaL3
```

`comm -12` over all declaration names in the two modules shows `contDiff_dirDeriv` is the *only* collision. Since `CriticalTrilinear` imports `GradientLambdaL3`, **no module can currently hold both `gradientLSix` and the U7 machinery.** Within lane authority (no edits to merged modules) I put `H1Trilinear` on the `GradientLSix` side — `import CriticalRegularity + CriticalL3Density + GradientLSix`, which is collision-free — and repeated lane 413's four small helpers under `…H1`-suffixed names (~35 lines, proofs unchanged, names distinct so the two modules will co-import the moment the duplicate goes, and every declaration stays axiom-auditable). The Hölder *engine* is not copied: §1 is a fresh exponent instance, not a re-proof of `(3,3,3)`.

**U10b needs both sides** (U10a here, U9/U8/U7 through `GradientLambdaL3`), and U13 needs everything, so the duplicate must be deleted upstream before T20 can be assembled. Minimal fix: drop `contDiff_dirDeriv` from `GradientLambdaL3.lean:210-212` and have it import `GradientLSix`, or move the general version down into `MeanZeroCalculus`/`FourierEmbeddings` (both modules already import those). This is the named-theorem version of the 2026-09-17 anonymous-instance lesson.

Failed tactic attempt, fixed: `norm_num [Fin.sum_univ_three]` does **not** discharge `∑ i, ![1/3,1/6,1/2] i = 1` —

```
error: NSFormalization/Section3/T20/H1Trilinear.lean:206:10: unsolved goals
case refine_2
⊢ 1 / 2 + ![1 / 3, 1 / 6, 1 / 2] 2 = 1
```

`![…] 0` and `![…] 1` reduce, `![…] 2` needs `Matrix.cons_val_two`/`head_cons`/`tail_cons`, which are not in `norm_num`'s set. Lane 413 never hit it because its exponent vector was the constant `1/3`. Fixed with an explicit `simp only [...]` before `norm_num`.

## 4. Commands run and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/429-T20-U10a-h1-trilinear`, after `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T20.CriticalTrilinear NSFormalization.Section3.T12.GradientLSix` | `Build completed successfully (10647 jobs)` — dependency warm-up |
| `lake build NSFormalization.Section3.T20.H1Trilinear` (attempt 1, importing `CriticalTrilinear` + `GradientLSix`) | **failed**: `import … GradientLSix failed, environment already contains 'NSFormalization.Section3.T12.contDiff_dirDeriv' from … GradientLambdaL3` |
| `lake build NSFormalization.Section3.T20.H1Trilinear` (attempt 2, exponent-sum side condition) | **failed**: `H1Trilinear.lean:206:10: unsolved goals … ⊢ 1 / 2 + ![1 / 3, 1 / 6, 1 / 2] 2 = 1` |
| `lake build NSFormalization.Section3.T20.H1Trilinear` (final) | `✔ Built NSFormalization.Section3.T20.H1Trilinear` / `Build completed successfully (10646 jobs)`, **0 errors** |
| `lake env lean ../formalization/NSFormalization/Section3/T20/H1Trilinear.lean` | exit 0, **0 bytes of output** |
| `lake env lean ../research/T20/probes/h1_trilinear_closes.lean` | exit 0, **0 bytes of output** |
| `lake env lean ../research/T20/axioms_u10a.lean` | exit 0; **16/16** declarations print exactly `[propext, Classical.choice, Quot.sound]`, 0 non-standard |
| `make check` | exit 0 (plan check, `check_contracts.py`, `test_contract_policy.py` 13 tests OK, `check_work_queue.py` "45 work items … consistent") |
| `make test` | exit 0, 0 errors; all registered contracts "checked; standard logical axioms only" |
| `grep -nE "sorry\|admit\|axiom\|native_decide\|maxHeartbeats"` over the three new files | only docstring prose and the `#print axioms` lines in the audit file |
| `git commit` | `1f01ab12 [429-T20-U10a] …`, working tree clean; no push/merge/rebase |
