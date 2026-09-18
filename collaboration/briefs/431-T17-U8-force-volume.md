# Lane 431-T17-U8-force-volume — T17 U8: torus support volume `O(ε³)` and duration `≤ 4ε²` of the periodized correction force

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/431-T17-U8-force-volume` (git branch `erenup/431-T17-U8-force-volume`, based on `origin/erenup/integration-section3`, which contains
`Section3/T17/{CorrectionProfile,Transport,LatticeDeriv,CorrectionDeriv,ForceDeriv,ForceProfile,Correction,ForceSupport}.lean` — lane 425's `force_support` (support in `Ioo (T−2ε²) (T+2ε²) ×ˢ
periodicSet (ball x₀ (ε·θRadius))`), `source_force_tsupport`, `latticeLift_spaceSupport`, and lane 373's `Transport.force_eq`). Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U8**
(`:193-203`), the canonical fields `spatialVolumeConst`, `spatialVolumeConst_nonneg`, `force_spatial_volume`, `force_time_length` in `Section3/T17/Correction.lean` (Spec form
`research/T17/Spec.lean:853-868`: `periodicTorusMeasure (torusSpatialSupport (correctionForce ν v D ε)) ≤ ENNReal.ofReal (spatialVolumeConst * ε^3)` and `volume (torusTemporalSupport …) ≤
ENNReal.ofReal (4 * ε^2)` — read the definitions of `torusSpatialSupport`/`torusTemporalSupport`/`torusSpaceTimeLift` in the canonical T17/T10 modules), `research/T17/REPORT_425.md`,
`research/T17/SPEC_ISSUES.md` (G1: the three U7 fields carry `hv : ContDiff ℝ ∞ v`; U8 inherits it only through `force_support`/`force_eq` — say where), the Section 4 analogue
`Section4/I02/Support.lean:43,53` (Euclidean spatial-volume and temporal-length bounds), `Section3/T13/TorusIdentity.lean` (`torusLift_torusPoint`, `fundamentalCube_ae_eq_halfOpenCube`, the
Haar-on-torus = Lebesgue-on-cube facts), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** Only the documented G1 `hv` may appear as an extra premise. An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T17/ForceVolume.lean` (namespace `NSFormalization.Section3.T17`): `def spatialVolumeConst : ℝ` (explicit, e.g. the volume of the unit ball times
`θRadius³`, or `(4/3)π·θRadius³`; nonnegative), and the two theorems `force_spatial_volume`, `force_time_length` with types literally the canonical fields at the concrete `correctionData` (probe by
`exact` as lane 425's probe does). Route: by `force_support` (425) the space-time support lies in `Ioo (T−2ε²) (T+2ε²) ×ˢ periodicSet (ball x₀ (ε·θR))`; the torus temporal support is contained in
that interval, whose Lebesgue measure is `4ε²`; the torus spatial support is contained in the torus image of `periodicSet (ball x₀ (ε·θR))`, i.e. the image of one ball of radius `ε·θR < r < 1/2`
(so the ball sits inside a single fundamental cell and the torus projection is injective on it): Haar measure of the projected ball = Lebesgue measure of the ball = `(4/3)π (ε θR)³` (use the
Haar = Lebesgue-on-cube facts of T13 `TorusIdentity`/`HaarCube`, `MeasureTheory.Measure.addHaar_ball`, monotonicity). Deliverables: the module, `research/T17/probes/force_volume_closes.lean`
(the two canonical fields closed by `exact`; instantiate at lane 425's non-vacuity witness), `research/T17/axioms_u8.lean`, `research/T17/ATTEMPTS_U8.md`, U8 status line in `T17_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.ForceVolume` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constant / files / gaps with error text / commands and results). Try `research/T17/REPORT_431.md`; if the
report-file guard blocks it, put the full report in your final message.
