# Lane 428-T20-U9-ybound — T20 U9: `yBound` verbatim (`eq:ybound`: under `ρ < cν`, `y(t) ≤ ∫₀ᵗ b ≤ ρ` on `Ico 0 T`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/428-T20-U9-ybound` (git branch `erenup/428-T20-U9-ybound`, based on lane 415's branch merged with `origin/erenup/integration-section3`:
`Section3/T20/{CriticalRegularity,MeanReduction,BIntegral,ConstantTransport,CriticalTrilinear,CriticalEnergy}.lean` — lane 415's `criticalEnergy` (U8, `C₀ = criticalTrilinearConst`) and its
reusable pieces (`hasSum_periodicPairing`, `hasDerivAt_tsum_critFreqEnergy`, `homENorm_toReal_eq_norm`, …), lane 390's `bIntegral` (U3: `criticalBIntegral (meanFreeForce g) ≤ criticalRho g`), lane 389's
mean-reduction fields). Read `CLAUDE.md`, **`research/T20/T20_SPLIT.md` §0 and unit U9** (`:154-166`), the canonical field `yBound` in `Section3/T20/CriticalRegularity.lean:314-322` (target
verbatim, with `c` the structure's constant: prove it for an explicit `c` — the split's `c := 1/(4·C₀)`-type choice or whatever the scalar lemma needs; state the exact constant, and how U13 will
install it), `paper/sections/03-torus.tex:445-466` (`eq:ybound` and the continuity argument), `research/T20/REPORT_415.md`, `REPORT_390.md`, the scalar core `Paper1/ScalarEnergy.lean:147
critical_norm_bound` (read its exact hypotheses: `henergy` = the differential inequality, `hK : C₀·K ≤ ν/2`, `hρK : ρ < K`, continuity of `y`, continuity/FTC of `N(t) = ∫₀ᵗ b`), the R³ template
`Section4/R43/ForcePath.lean` (slice continuity + interval integrability + primitive FTC of the force path) and `CriticalMomentum.lean`, T11 `HighOrder.lean:146 continuousOn_torusSobolevNormAt_velocity`
(continuity of `t ↦ y(t)` — transport to order 1/2 as lane 415 transported the derivative), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T20/YBound.lean` (namespace `NSFormalization.Section3.T20`): `def criticalSmallness : ℝ` (the `c`, positive, `criticalSmallness_pos`) and
`theorem yBound` whose type is literally the canonical field at `c := criticalSmallness` (probe: `example : yBoundFieldType criticalSmallness := yBound` mirroring lane 415's probe pattern).
Route: (i) `∫₀ᵗ b ≤ ρ`: from `bIntegral` (U3) and monotonicity of the lintegral in the domain (`Ioc 0 t ⊆` the full force-time domain); (ii) `y(t) ≤ ∫₀ᵗ b`: the scalar bootstrap
`critical_norm_bound` applied to `y(t).toReal` with U8's differential inequality, `K := ν/(2·C₀)`, `ρ < c·ν ≤ K` — supplying continuity of `y` on `Ico 0 T` (order-1/2 transport of T11's
continuity), continuity and FTC of `N(t) = (∫⁻ s in Ioc 0 t, b s).toReal` (needs `b` locally integrable: `criticalB (meanFreeForce g)` is continuous in `t` for `g ∈ forceClassT` — the torus copy of
`R43.ForcePath`), finiteness of everything `.toReal` touches (`ρ < ⊤` from the smallness hypothesis; `y(t) < ⊤` from `reductionRegular`), and then convert back to `ℝ≥0∞` with `ENNReal.toReal_le_toReal`/
`ofReal_toReal`. `y(0) = 0` (zero initial velocity). If the FTC/continuity of the force path is the long pole, deliver the bootstrap under an explicit continuity/FTC lemma statement (probe-level
only) and record the exact residual. Deliverables: the module, `research/T20/probes/ybound_closes.lean` (field-type match; non-vacuity at lane 415's zero-force zero-solution instance), `research/T20/axioms_u9.lean`,
`research/T20/ATTEMPTS_U9.md`, U9 status line in `T20_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.YBound` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement and constant / files / gaps with error text / commands and results). Try `research/T20/REPORT_428.md`; if the report-file
guard blocks it, put the full report in your final message.
