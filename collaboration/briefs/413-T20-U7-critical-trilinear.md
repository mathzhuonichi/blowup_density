# Lane 413-T20-U7-critical-trilinear — T20 U7: the mean-zero critical trilinear estimate `|⟪(v·∇)v, Λv⟫| ≤ C₀ · y · z²` on T³

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/413-T20-U7-critical-trilinear` (git branch `erenup/413-T20-U7-critical-trilinear`, based on `origin/erenup/integration-section3`
**after** lanes 401 (`Section3/T12/CriticalL3Density.lean`: verbatim `velocityCriticalL3`, constant `CcriticalHalf`) and 405 (`Section3/T12/GradientLambdaL3.lean`:
`gradientLambdaCriticalL3`, constant `CcriticalThreeHalves = 4 * CcriticalHalf`, plus `periodicLpENorm_gradientTensor_le_sum`, `eLpNorm_torus_le_sum_of_norm_le`,
`isMeanZeroT_lambda`, `isMeanZeroT_dirDeriv`) merged). Read `CLAUDE.md`, **`research/T20/T20_SPLIT.md` §0, unit U7 and unit U8** (U8 is the consumer: match the spelling it
needs — `criticalY`/`criticalZ` in `Section3/T20/CriticalRegularity.lean:70-90`, the `C₀` of the canonical structure, the Haar pairing spelling of T11 `EnergyIdentity.lean`
(`∫ y : PeriodicTorus, torusLift (fun x ↦ inner ℝ (…) (…)) y ∂periodicTorusMeasure`), `IsPeriodicLambda`/`lambda_exists` in `Section3/T12/FourierEmbeddings.lean`),
`research/T12/REPORT_401.md`, `research/T12/REPORT_405.md`, the R³ analogue `Section4/R43/Trilinear.lean` (`lintegral_enorm_mul_three_le :176` three-factor Hölder,
`criticalAdvectionHolder :228`, `trilinearConst :314`, `criticalTrilinearEstimate_of_hcrit :335`), `Section3/T12/HaarCube.lean` (Haar ↔ cube `L^p` transfer),
`paper/sections/03-torus.tex:425-440` (`eq:criticalenergy` and the trilinear step), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean` (namespace `NSFormalization.Section3.T20`): for a smooth periodic mean-zero spatial field `v`
with `IsPeriodicLambda v Lv`,
`|∫ y : PeriodicTorus, torusLift (fun x ↦ inner ℝ (advection v v x) (Lv x)) y ∂periodicTorusMeasure| ≤ criticalTrilinearConst * (periodicHomogeneousENorm (1/2) v).toReal *
(periodicHomogeneousENorm (3/2) v).toReal ^ 2` — state it in **exactly** the spatial-slice spelling U8 will apply at each time to `meanFreeVelocity g w.velocity` (read U8 and
`criticalY`/`criticalZ`; if they are `ℝ≥0∞`-valued with `.toReal`, add the finiteness hypotheses U8 can supply — `MemPeriodicHomogeneous (3/2) v` gives `z < ⊤`, and
`y ≤ z`-type comparisons exist in `SpectralGap`/`FourierEmbeddings` — and say which). Also give the `ℝ≥0∞` form without `toReal` if it is cleaner, with the `toReal` corollary.
Route: (1) pointwise `‖inner (advection v v) Lv‖ ≤ ‖v‖ ‖∇v‖ ‖Lv‖` (advection = `(v·∇)v`, bounded by `‖v‖·‖gradientTensor v‖` — read the vendor `advection` definition and mirror
`R43.criticalAdvectionHolder`); (2) three-factor Hölder on the cube measure `volume.restrict fundamentalCube` (transfer the Haar integral to the cube with `HaarCube` lemmas,
then `lintegral_enorm_mul_three_le`-style with exponents `3,3,3`); (3) `velocityCriticalL3` (401) for `‖v‖₃`, `gradientLambdaCriticalL3` (405) for `‖∇v‖₃ + ‖Lv‖₃`
(each summand ≤ the sum); (4) `criticalTrilinearConst := CcriticalHalf * CcriticalThreeHalves ^ 2` (or the tighter product you actually get), with `_pos`.
Deliverables: the module, `research/T20/probes/critical_trilinear_closes.lean` (the estimate at a nonzero smooth mean-zero witness such as `meanZeroPartT (x ↦ cos(2π x₀)·e₀)` with
`Lv` from `lambda_exists`, plus a shape check that U8 can consume it — write the `example` in U8's slice spelling), `research/T20/axioms_u7.lean`, `research/T20/ATTEMPTS_U7.md`,
U7 status line in `T20_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.CriticalTrilinear` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement and constant / files / gaps with error text / commands and results). Try `research/T20/REPORT_413.md`;
if the report-file guard blocks it, put the full report in your final message.
