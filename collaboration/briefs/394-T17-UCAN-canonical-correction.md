# Lane 394-T17-UCAN-canonical-correction — T17 U-CAN (first half of U12): the canonical `CorrectionAPI` restated over the canonical T15/T16 records (bare `(x₀, T)` spelling), prerequisite for T18 U1

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/394-T17-UCAN-canonical-correction` (git branch `erenup/394-T17-UCAN-canonical-correction`, based on lane 384's branch merged with
`origin/erenup/integration-section3`: `Section3/T15/Scaling.lean` (lane 384: the raw-packet-field `PlacementData`/`ScalingAPI`), `Section3/T16/{LocalPotential,Assembly}.lean` (`CutoffData`,
`LocalPotentialAPI`, `localPotentialData`), `Section3/T13/Assembly.lean` (`LocalizationAPI`), `Section3/T17/{CorrectionProfile,Transport,LatticeDeriv,CorrectionDeriv,ForceDeriv}.lean`
(lanes 370/373/369/385: the proved T17 fields in the bare `(x₀, T)` spelling with the `hv : ContDiff ℝ ∞ v` premise)). Read `CLAUDE.md` ("合同 import 规则", "结构体例外"),
**`research/T17/Spec.lean:752-…` (`CorrectionAPI ν place D … : Type` with all its fields — the token-for-token source), `research/T17/T17_SPLIT.md` (U12 and the lead note in
`research/T18/T18_SPLIT.md` §0 explaining this unit), `research/T17/SPEC_ISSUES.md` (G1: add `reference_smooth`? — lead decision below; G3: bare `(x₀, T)`)**, `research/T15/REPORT_384.md`
(the raw-field `PlacementData` and its probe conversions), the canonical-module templates `Section3/T16/LocalPotential.lean` + `research/T16/probes/api_on_canonical.lean`, and the top 40
lines of `logs/LESSONS.md`.

## Lead decisions for this unit
- Bare `(x₀, T)`: the canonical `CorrectionAPI` takes `place : T15.PlacementData …` (lane 384's raw-field record) and uses `place.x₀`/`place.T` (G3 closed).
- G1: the canonical structure keeps the Spec's field list **unchanged** (no added `reference_smooth` field); the proved units' `hv` premise is discharged at assembly (U12) either by a
  chart truncation of `v` or by an explicit hypothesis of the assembly theorem — do NOT change the Spec's `CorrectionAPI` here; record in the module docstring that the assembly's
  hypotheses are still open per SPEC_ISSUES G1.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; no proofs of the API fields (statement-restatement unit); no edits to existing modules; new files only.
- **No stubs**: every field is the Spec's text (namespace and the canonical record types change only). Every declaration `[propext, Classical.choice, Quot.sound]`.

## Goal
1. `formalization/NSFormalization/Section3/T17/Correction.lean` (namespace `NSFormalization.Section3.T17`): the T17 definitions the structure uses (import the ones already canonical in
   `CorrectionProfile.lean`/`Transport.lean`/`ForceProfile.lean` if lane 375 has landed on your base — check; otherwise restate verbatim), and `structure CorrectionAPI` restated
   token-for-token over the canonical `T15.PlacementData` (raw fields), `T16.CutoffData`/`LocalPotentialAPI`, `T13.LocalizationAPI`, with every field's docstring and paper line kept;
   plus `def correctionStatement : Prop` in the Spec's shape.
2. Probe `research/T17/probes/correction_canonical.lean`: import `Contracts.*`, restate the Spec's `CorrectionAPI` token-for-token (namespace only), give the fieldwise conversions Spec ↔ canonical
   (through lane 384's `PlacementData` conversions), and show that the already-proved canonical units close their fields of the canonical structure by `exact` (U3 profile fields, U4 force
   profile fields, U5/U6 derivative bounds — under their `hv`/`ε₀ ≤ 1` premises, stated as the probe's hypotheses).
3. Records: `research/T17/ATTEMPTS_UCAN.md` (field mapping table), `research/T17/axioms_ucan.lean`, status in `research/T17/T17_SPLIT.md` (U-CAN entry), report `research/T17/REPORT_394.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Correction` (0 errors), `lake env lean` on the module (0 output), on the probe and axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T17/REPORT_394.md`.
