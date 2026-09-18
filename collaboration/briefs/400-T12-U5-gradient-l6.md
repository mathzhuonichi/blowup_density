# Lane 400-T12-U5-gradient-l6 — T12 U5: `gradientLSix` verbatim (`‖∇v‖_{L⁶(T³)} ≤ C₆ ‖Δv‖_{L²(T³)}`, route (c))

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/400-T12-U5-gradient-l6` (git branch `erenup/400-T12-U5-gradient-l6`, based on `origin/erenup/integration-section3`, which
contains `Section3/T12/{MeanZeroCalculus,SpectralGap,FourierEmbeddings,TameProduct,Cutoff,HaarCube,CutoffGagliardo}.lean`). Read `CLAUDE.md`, **`research/T12/T12_SPLIT.md` §0
and unit U5** (target verbatim in `research/T12/probes/api_on_canonical.lean:184-187`, route (c)), `research/T12/REPORT_{365,366,377}.md` and `research/T12/ATTEMPTS_U4.md`
(pitfalls: private lemmas, `mul_le_mul_left'` unknown → `gcongr`), the registered whole-space `A05.gradient_l6` (`verification/Bindings/GradientL6.lean:42`,
`Section4/A05/GradientL6.lean:64 eLpNorm_gradTensor_six_le` — read its exact hypothesis and norm spellings), `Section3/T12/FourierEmbeddings.lean:165 hTwo_le_laplacian`,
`paper/sections/appendix-b-embeddings.tex` (the `L⁶` gradient line), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming anything is "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T12/GradientLSix.lean` (namespace `NSFormalization.Section3.T12`): `theorem gradientLSix` verbatim —
`∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v → periodicLpENorm 6 (gradientTensor v) ≤ ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)` with explicit
`def Csix` and `Csix_pos`. Route (c): `periodicLpENorm 6 (gradientTensor v) = eLpNorm (∇v) 6 (volume.restrict Q)` (lane 366 `HaarCube`: `periodicLpENorm_eq_restrict`, vector
version) `= eLpNorm (∇(cutoffMul v)) 6 (restrict Q)` (`cutoffMul v = v` on a neighbourhood of `Q`, lane 365 `Cutoff.lean`) `≤ eLpNorm (∇(cutoffMul v)) 6 volume`
(`Measure.restrict_le_self`) `≤ Csix₀ · eLpNorm (Δ(cutoffMul v)) 2 volume` (registered `A05.gradient_l6` on the smooth compactly supported `cutoffMul v`, hypothesis via
`memHInfty_cutoffMul` or whatever its datum hypothesis is); Leibniz `Δ(χv) = χΔv + 2∇χ·∇v + vΔχ`: the `χΔv` term on `Q` returns `‖Δv‖_{L²(T³)}` (and outside `Q` it is bounded by
`‖Δv‖_{L²}` of finitely many translates, or by the cube-count bound of the larger cube); the commutator terms are supported in the larger cube and bounded by
`‖v‖_{H²(T³)} ≲ ‖Δv‖_{L²}` (`hTwo_le_laplacian`), using periodicity to convert the larger-cube `L²` norms to finitely many copies of the cube norm. Set `Csix` from these constants.
Deliverables: the module, `research/T12/probes/gradient_l6_closes.lean` (closes the API field form by `exact`, non-vacuous on a nonzero mean-zero smooth periodic `v`),
`research/T12/axioms_u5.lean`, `research/T12/ATTEMPTS_U5.md`, U5 status line in `T12_SPLIT.md`, one line in `logs/LESSONS.md` if you learn a pin-specific pitfall.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.GradientLSix` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement and constant / files / gaps with error text / commands and results). Try to write it to
`research/T12/REPORT_400.md`; if the report-file guard blocks that, put the full report in your final message instead.
