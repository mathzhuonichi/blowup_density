# Lane 401-T12-U4b-critical-l3-density — T12 U4b: the verbatim `velocityCriticalL3` from the smooth theorem by torus density

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/401-T12-U4b-critical-l3-density` (git branch `erenup/401-T12-U4b-critical-l3-density`, based on lane 396's branch merged with
`origin/erenup/integration-section3`; it contains `Section3/T12/CriticalL3.lean` with `velocityCriticalL3_smooth (v) (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) :
periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1/2) v`, `periodicSobolevENorm_zero_le_half`, `l2Q_le_homogeneous_half`). Read `CLAUDE.md`,
`research/T12/REPORT_396.md` §3 (the exact residual and the four steps (i)–(iv)), `research/T12/ATTEMPTS_U4.md`, `research/T12/T12_SPLIT.md` §0/U4/risk 2,
`Section3/T12/MeanZeroCalculus.lean` (`MemPeriodicHomogeneous`, `periodicHomogeneousENorm`, `IsMeanZeroT` — how the homogeneous norm is built on the T10 Fourier datum),
`Section3/T10/PeriodicData.lean` (datum path, strong measurability), `Section3/T12/SpectralGap.lean` (`reweightDatum`, weight algebra), `Section3/T15/ParsevalZero.lean`
(order-zero Parseval), and the top 40 lines of `logs/LESSONS.md`. In-tree hits for mollification/reconstruction: `Paper1/PeriodicH2Uniform.lean`, `Paper1/FourierReconstructionAdapter.lean`
(grep `mollif`, `partialSum`, `truncat`, `fourierSeries` across `Section3/T10`, `Paper1/`, `Source/` before deciding).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T12/CriticalL3Density.lean` (namespace `NSFormalization.Section3.T12`): `theorem velocityCriticalL3 (v : SpatialField)
(hv : MemPeriodicHomogeneous (1/2) v) : periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1/2) v` — the verbatim API field
(`research/T12/probes/api_on_canonical.lean:148-151`), same constant `CcriticalHalf` as the smooth theorem. Choose the approximation that fits the existing datum machinery:
(A) Fourier truncation `v_N := Σ_{0<|k|≤N} v̂(k) e_k` — smooth, periodic, mean-zero, `periodicHomogeneousENorm (1/2) v_N ≤ periodicHomogeneousENorm (1/2) v` (coefficientwise
restriction; reuse the `reweightDatum`/iInf-over-paths pattern), `v_N → v` in `L²(Q)` hence a.e. along a subsequence; or (B) periodic mollification with symbol `|φ̂_ε(k)| ≤ 1`.
Then the `L³` lower semicontinuity: `periodicLpENorm 3 v = eLpNorm v 3 (restrict Q)` (HaarCube) and Mathlib's Fatou for `eLpNorm` (grep `eLpNorm_lim_le_liminf_eLpNorm` /
`eLpNorm_liminf` in `Mathlib/MeasureTheory/Function/LpSeminorm`), applied to the a.e.-convergent subsequence; conclude `≤ liminf (ofReal C · ‖v_N‖_{Ḣ^{1/2}}) ≤ ofReal C · ‖v‖_{Ḣ^{1/2}}`.
If the truncation's a.e. convergence needs an `L²` Parseval/reconstruction statement that is missing, isolate that single statement as the exact residual (Outcome B) — do not assume it.
Deliverables: the module, `research/T12/probes/critical_l3_density_closes.lean` (closes the field by `exact` on the canonical API shape; non-vacuous on a nonzero `v`),
`research/T12/axioms_u4b.lean`, `research/T12/ATTEMPTS_U4B.md`, U4b status line in `T12_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.CriticalL3Density` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Try `research/T12/REPORT_401.md`; if the report-file
guard blocks it, put the full report in your final message.
