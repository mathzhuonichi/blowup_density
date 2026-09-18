# Lane 438-T17-U11-sobolev — T17 U11: `eq:HHs` — the `L¹_t H^s_x` bound of the periodized correction force for `0 ≤ s ≤ 1` (+ honest path + constant)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/438-T17-U11-sobolev` (git branch `erenup/438-T17-U11-sobolev`, based on `origin/erenup/integration-section3`, which contains
`Section3/T17/{CorrectionProfile,Transport,LatticeDeriv,CorrectionDeriv,ForceDeriv,ForceProfile,Correction,ForceSupport}.lean` (lanes 425/431/434's `ForceVolume`/`Energy` are on their own branches, in review —
their single-copy techniques are described in `research/T17/REPORT_{431,434}.md`), the registered T13 localization contract `Contracts/V1/Localization.lean` (`T02.localization`: `wholeSpace_identity`,
`torus_identity`, `localization` for `0<s<1`, `endpoint_zero`/`endpoint_one`) with `Bindings/Localization.lean` and the canonical `Section3/T13/*` modules (single-copy adapter, `Localization.lean`,
`ConstantEndpoints.lean`, `KernelComparison.lean`), the canonical `Section3/T17/Correction.lean` fields `sobolevConst`, `sobolevConst_pos`, `forceSobolev_memLp`, `force_sobolev_bound` (Spec form
`research/T17/Spec.lean:940-960`), Paper1's Euclidean force Sobolev bounds (grep `forceSobolev`/`physical_force_sobolev` in `Paper1/Correction*.lean` and the registered `I02` force fields in
`Contracts/V1/Correction.lean`)). Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U11** (`:223-234`) and `research/T17/RECONCILIATION.md` §4 ⑦, `research/T17/SPEC_ISSUES.md` (G1),
`research/T17/REPORT_{373,425,434}.md`, `research/T13/REPORT_359.md` (localization assembly and what the registered API gives, incl. the ε-independent constant), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T17/Sobolev.lean` (namespace `NSFormalization.Section3.T17`): `def sobolevConst : ℝ → ℝ` (explicit, positive on `[0,1]`: `sobolevConst_pos`),
`forceSobolev_memLp` (`MemForceSobolevT 1 s (correctionForce ν v D ε)` for `0 ≤ s ≤ 1`, `ε ∈ Ioc 0 D.ε₀`) and `force_sobolev_bound` (`forceSobolevENormT 1 s (correctionForce …) ≤ ofReal (sobolevConst s ·
ε^{…})` — read the exact exponent in the canonical field), with types literally the canonical fields at the concrete `correctionData` (probe by `exact`; premise block as lanes 425/434 incl. G1 `hv`).
Route: each force slice is `periodize` of its compact central copy (single-copy support inside the cube, lane 425/434 technique); the registered localization API (`T02.localization`, via the canonical
T13 theorems) compares the torus `H^s` norm of a periodized compactly supported field with the whole-space `H^s` norm of the copy with one ε-independent constant (`0<s<1` via `localization`, endpoints
via `endpoint_zero`/`endpoint_one`); the Euclidean `L¹_t H^s_x` bound of the single-copy force is Paper1's/`I02`'s registered force Sobolev bound; integrate in time. Honest path: `MemForceSobolevT 1 s`
from the slice `H^s` data path (T10 `force_coefficient_path`-style, or the localization API's datum transport). If the endpoint or a fractional case genuinely lacks an in-tree bridge, deliver the
other cases and record the exact residual. Deliverables: the module, `research/T17/probes/sobolev_closes.lean` (fields closed by `exact`; non-vacuity at lane 434's cube-centred witness),
`research/T17/axioms_u11.lean`, `research/T17/ATTEMPTS_U11.md`, U11 status line in `T17_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Sobolev` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constant / files / gaps with error text / commands and results). Try `research/T17/REPORT_438.md`; if the report-file guard
blocks it, put the full report in your final message.
