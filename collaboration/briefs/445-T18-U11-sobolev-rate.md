# Lane 445-T18-U11-sobolev-rate — T18 U11: `eq:Hsclose` Sobolev closeness of the force difference + the `s < 0` tail

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/445-T18-U11-sobolev-rate` (git branch `erenup/445-T18-U11-sobolev-rate`, based on `origin/erenup/integration-section3`: the T18 layer
`Section3/T18/{Insertion (U1: InsertionData threading scaling : ScalingAPI, correction : CorrectionAPI, reference, raw packet clauses), ForceClass (U2: g_ε − g = H_ε + F_ε ∈ forceClassT), …}.lean`,
the canonical records `Section3/T15/Scaling.lean` (`ScalingAPI.packetSobolevBound`, `forceSobolev_memLp`, `sobolevConst`/`_pos` — read the exact field texts), `Section3/T17/Correction.lean`
(`CorrectionAPI.force_sobolev_bound`, `forceSobolev_memLp`, `sobolevConst`/`_pos`), and the torus force Sobolev norm `forceSobolevENormT`/`MemForceSobolevT` (registered `Contracts/V1/TorusLocalTheory.lean`
+ canonical T10 copy)). **All facts you need are fields of the threaded records** — U11 is bookkeeping over them plus norm monotonicity in `s`. Read `CLAUDE.md`, **`research/T18/T18_SPLIT.md` §0 and unit
U11** (`:190-201`), the Spec fields `research/T18/Spec.lean:1926-1970` (`forceDiffSobolevConst`, `_pos` on `0 ≤ s < 1/2`, `forceDifference_sobolev_memLp`, `forceDifference_sobolev_bound` with
`C_s(ε^{1/2−s} + ε^{3/2−s})`, `forceDifference_negativeSobolev_tendsto` for `s < 0`, `negative_s_memLp`), `research/T18/REPORT_{422,426,433}.md` and probes (`InsertionData` conventions, Spec↔canonical
conversions), `Section3/T17/Sobolev.lean` on lane 438's branch is NOT on this base — but its reusable lemma `norm_datum_mono` (`‖·‖_{H^s} ≤ ‖·‖_{H^t}` for `s ≤ t` on the T10 datum) is described in
`research/T17/REPORT_438.md` §2: grep the tree for an existing monotonicity (`periodicSobolevSq_mono`, `Paper1.periodicVectorSobolevNorm_mono`, `T10.norm_datum_*`) and reprove locally if absent; and the top
40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first (`lake build <module>`), never assume `.olean`s exist.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T18/SobolevRate.lean` (namespace `NSFormalization.Section3.T18`), theorem types = the six Spec fields under `InsertionData` projections:
`forceDiffSobolevConst s := scaling.sobolevConst s + correction.sobolevConst s` (or whatever sum makes the bound hold — read both records' bound shapes: `packetSobolevBound` gives `‖F_ε‖ ≤ C_s(ε^{1/2−s} +
lower-order)`, `force_sobolev_bound` gives `‖H_ε‖ ≤ C_s(ε^{3/2} + ε^{3/2−s})`; absorb the lower-order terms using `0 ≤ s`, `ε ≤ 1` (`place.eps_le_one`)), `_pos`; `forceDifference_sobolev_memLp` (path guard:
`MemForceSobolevT 1 s` of a sum from the two records' guards — `MemLp.add` on the time paths); `forceDifference_sobolev_bound` (triangle inequality for `forceSobolevENormT 1 s` — prove it as a
lemma from the infimum-over-paths definition: given paths for each summand, their sum is a path for the sum, and `eLpNorm_add_le` at exponent 1 in time with the slice norms subadditive on the
`PeriodicSobolev s` normed space); `forceDifference_negativeSobolev_tendsto` (for `s < 0`: `forceSobolevENormT 1 s ≤ forceSobolevENormT 1 0` by monotonicity of the datum norm in `s`, and the `s = 0`
bound `≤ C_0(ε^{1/2} + ε^{3/2}) → 0`); `negative_s_memLp` (a path at order 0 is a path at order `s < 0` after the order-lowering map — reuse T11's `torusMultiplierCLM`/lane 428's `critLower` pattern
described in `research/T20/REPORT_428.md`, or the datum monotonicity). Deliverables: the module, `research/T18/probes/u11_closes.lean` (Spec-form fields via the U1 conversions),
`research/T18/axioms_u11.lean`, `research/T18/ATTEMPTS_U11.md`, U11 status line in `T18_SPLIT.md`. If a field needs a fact no record carries (say exactly which), deliver the others and record the exact residual.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.SobolevRate` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T18/REPORT_445.md`.
