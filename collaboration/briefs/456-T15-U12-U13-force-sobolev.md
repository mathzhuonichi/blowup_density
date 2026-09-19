# Lane 456-T15-U12-U13-force-sobolev — T15 U12 (`sobolevConst`, `sobolevConst_pos`, `forceSobolev_memLp`) + U13 (`packetSobolevBound`, `eq:packetHs`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/456-T15-U12-U13-force-sobolev` (git branch `erenup/456-T15-U12-U13-force-sobolev`, = lane 450's branch + `origin/erenup/integration-section3`:
`Section3/T15/{Bridges,ParsevalZero,HaarBridge,Scaling,Placement,SingleCopy,Energy,Mixed,Blowup,ForceMem,Equation,Pressure,SobolevPath}.lean` — lane 450's all-order datum paths for the periodized
velocity (`periodized_sobolev`, the pattern for building a continuous `PeriodicSobolev s` path of a smooth periodic compactly-supported-in-time field), lane 421's single copy, lane 439's chart lemmas;
the registered T13 localization contract `T02.localization` (`Contracts/V1/Localization.lean`, `Bindings/Localization.lean`) and the canonical `Section3/T13/{Localization,ConstantEndpoints,TorusIdentity,
WholeSpaceIdentity,LocalizationKernel,KernelComparison,Assembly}.lean` (the torus-vs-whole-space `H^s` comparison for a periodized compactly supported field with one ε-independent constant: `localization`
for `0<s<1`, `endpoint_zero`/`endpoint_one` at `s = 0, 1` — read the assembled API in `Section3/T13/Assembly.lean` and its hypotheses, e.g. support in a ball of radius `< 1/2` inside the cell);
lane 438's `Section3/T17/Sobolev.lean` (the **same** problem for the correction force: it went through Paper1's periodic endpoint rates instead of T13 because the T13 route needs an `ENNReal` adapter
from `dotHomogeneousENorm` to Paper1's norm — read `research/T17/REPORT_438.md` §1/§3 and its reusable lemmas `periodicSobolevENorm_slice_eq` (T10 datum norm = Paper1 `periodicVectorSobolevNorm` at
every real order), `periodicSobolevENorm_translate`, `norm_datum_mono`, `force_coefficient_path_real`, `shiftedForce`/`periodize_shiftedForce`), and the Section 4 whole-space packet Sobolev rates
(`Contracts/V1/Scaling.lean` `packetSobolevBound`-type field of `I03.scaling` and its canonical proof `Section4/I03/Sobolev*.lean`: `‖F_ε‖_{L¹_tH^s(ℝ³)} ≤ C_s(ε^{1/2} + ε^{1/2−s})` — grep `sobolev` in
`Section4/I03` and `Bindings/Scaling.lean`). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0, units U12 (`:152-156`) and U13 (`:158-169`)**, the canonical fields `sobolevConst :403`,
`sobolevConst_pos :410`, `forceSobolev_memLp :420`, `packetSobolevBound :432` in `Section3/T15/Scaling.lean`, `paper/sections/03-torus.tex:133-158` (`eq:packetHs`), `research/T15/REPORT_{421,438,450}.md`,
`research/T13/REPORT_359.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T15/SobolevBound.lean` (namespace `NSFormalization.Section3.T15`): `def sobolevConst : ℝ → ℝ` (explicit, positive on `[0,1]`: `sobolevConst_pos`),
`forceSobolev_memLp` (honest `L¹_t H^s(T³)` path of the periodized scaled force for `0 ≤ s ≤ 1`: from the smooth periodic compactly-supported-in-time slices, via the T10 datum path construction
restricted to real `s ∈ [0,1]` — lane 438's `force_coefficient_path_real` pattern), and `packetSobolevBound` (`forceSobolevENormT 1 s (periodizedScaledForce …) ≤ ofReal (sobolevConst s · (ε^{1/2} +
ε^{1/2−s}))`), types literally the `ScalingAPI` fields over the raw-field `PlacementData` (probe by `exact`). Route (choose after reading both): (A) T13: each slice of the periodized force is the
periodization of the single copy supported in a ball of radius `ε·θR < r < 1/2` inside the cell, so the T13 localization API compares the torus `H^s` norm with the whole-space `H^s` norm of the copy
with an ε-independent constant, and the Section 4 whole-space rate gives `≤ C_s(ε^{1/2} + ε^{1/2−s})`; if the `ENNReal` adapter between the T13/D01 homogeneous norm and the norm used by the whole-space
rate is missing (lane 438's finding), state it exactly and switch to (B): the Paper1 periodic Fourier-series endpoint rates for the scaled packet force (grep `Paper1/Periodic*Force*` for the
packet/scaled-force analogue of `correction_scalar_whole_endpoint_rates`; interpolate `s ∈ (0,1)` by `norm_datum_mono`-type monotonicity or by the endpoint product lemma as 438 did). Deliverables: the
module, `research/T15/probes/sobolev_bound_closes.lean` (fields by `exact` + the nonzero concrete packet instance), `research/T15/axioms_u12_u13.lean`, `research/T15/ATTEMPTS_U12_U13.md`, status
lines for U12/U13 in `T15_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific. If `packetSobolevBound` cannot be closed on the whole range, deliver U12 fully plus the endpoint cases and the exact
residual for the fractional range.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.SobolevBound` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constant / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_456.md`.
