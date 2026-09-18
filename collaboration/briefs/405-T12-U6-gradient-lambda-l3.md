# Lane 405-T12-U6-gradient-lambda-l3 — T12 U6: `gradientLambdaCriticalL3` verbatim (`‖∇v‖₃ + ‖Λv‖₃ ≤ C ‖v‖_{Ḣ^{3/2}}`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/405-T12-U6-gradient-lambda-l3` (git branch `erenup/405-T12-U6-gradient-lambda-l3`, based on `origin/erenup/integration-section3`,
which contains `Section3/T12/{MeanZeroCalculus,SpectralGap,FourierEmbeddings,TameProduct,Cutoff,HaarCube,CutoffGagliardo,CriticalL3}.lean`; lane 396's
`CriticalL3.lean` has `velocityCriticalL3_smooth (v) (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) : periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf *
periodicHomogeneousENorm (1/2) v`). Read `CLAUDE.md`, **`research/T12/T12_SPLIT.md` §0 and unit U6** (target verbatim `research/T12/probes/api_on_canonical.lean:170-175`, route),
`research/T12/REPORT_396.md`, `research/T12/ATTEMPTS_U4.md` (pitfalls: private lemmas, `mul_le_mul_left'` unknown → `gcongr`), `Section3/T12/FourierEmbeddings.lean`
(`IsPeriodicLambda` / `lambdaField_component :289`, `lambdaCoeff :225`, `lambda_exists`), `Section3/T12/SpectralGap.lean` (`periodicFrequencyWeight_rpow_le_gap_mul_homogeneous :90`,
`reweightDatum :127`), `paper/sections/appendix-b-embeddings.tex`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean` (namespace `NSFormalization.Section3.T12`): `theorem gradientLambdaCriticalL3` verbatim —
`∀ v Lv, SmoothPeriodicT v → MemPeriodicHomogeneous (3/2) v → IsPeriodicLambda v Lv → periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
ENNReal.ofReal CcriticalThreeHalves * periodicHomogeneousENorm (3/2) v` with explicit `def CcriticalThreeHalves` and `_pos`. Route: apply `velocityCriticalL3_smooth` to each
component derivative `∂_j v` (smooth periodic, mean-zero because `∂_j` kills the zero mode) and to `Lv` (mean-zero; **check what `IsPeriodicLambda v Lv` gives about `Lv`** —
if it pins `Lv` as a smooth periodic field (e.g. through the Fourier series of a smooth `v`), prove `SmoothPeriodicT Lv`/`IsMeanZeroT Lv` from it; if `Lv` is only determined
a.e., then the field's `periodicLpENorm 3 Lv` is representative-dependent only through a null set and you need the general `velocityCriticalL3` of lane 401 (not yet on this
base) — in that case deliver the `∇v` half unconditionally plus the `Lv` half under an explicit `SmoothPeriodicT Lv` premise, and state the exact residual). Then the Fourier
order-shift inequalities `periodicHomogeneousENorm (1/2) (∂_j v) ≤ periodicHomogeneousENorm (3/2) v` (multiplier `2πk_j`, `|2πk_j| ≤ 2π|k|`) and
`periodicHomogeneousENorm (1/2) Lv = periodicHomogeneousENorm (3/2) v` (multiplier `2π|k|`), via the `SpectralGap.lean` weight algebra and `reweightDatum`; finally assemble the
three component `L³` norms into `periodicLpENorm 3 (gradientTensor v)` (read how `gradientTensor` and `periodicLpENorm` on tensor fields are defined in `MeanZeroCalculus.lean`).
Deliverables: the module, `research/T12/probes/gradient_lambda_l3_closes.lean` (closes the API field by `exact`; non-vacuous on a nonzero `v`), `research/T12/axioms_u6.lean`,
`research/T12/ATTEMPTS_U6.md`, U6 status line in `T12_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.GradientLambdaL3` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement and constant / files / gaps with error text / commands and results). Try `research/T12/REPORT_405.md`;
if the report-file guard blocks it, put the full report in your final message.
