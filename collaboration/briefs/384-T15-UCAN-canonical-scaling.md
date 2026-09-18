# Lane 384-T15-UCAN-canonical-scaling — T15 U-CAN: the canonical `PlacementData` and `ScalingAPI` over raw packet fields (prerequisite for T17 U12 and T18)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/384-T15-UCAN-canonical-scaling` (git branch `erenup/384-T15-UCAN-canonical-scaling`, based on `origin/erenup/integration-section3`:
`Section3/T15/{Bridges,ParsevalZero,HaarBridge}.lean` (lane 362's canonical rescaling definitions), `Section3/T14/PacketEnergy.lean` (T14 over raw packet fields — the pattern to follow),
`Section3/T13/Assembly.lean` (`LocalizationAPI`), `Section3/T16/LocalPotential.lean`). Read `CLAUDE.md` ("合同 import 规则": `formalization/` cannot import `Contracts.*`; "结构体例外"),
**`research/T15/Spec.lean:560-924`** (`PlacementData {ν} (P : PacketAPI ν)` and `ScalingAPI {ν} (P : PacketImportAPI ν) (place : PlacementData P)` with all 21 fields — the token-for-token
source), `research/T15/T15_SPLIT.md` §0 (and the lead note in `research/T18/T18_SPLIT.md` §0 explaining why this unit exists), `research/T14/probes/api_on_canonical.lean` (how T14 states
things over raw fields and converts in the probe), `verification/Contracts/V1/Packet.lean` (`PacketAPI` fields) and `Contracts/V1/PacketImport.lean`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; no proofs of the API fields (this is a statement-restatement unit); no edits to existing modules; new files only.
- **No stubs**: every field is the Spec's text, with `P.velocity`/`P.pressure`/`P.force`/`P.carrier`/`P.energyBound`/`P.dissipationBound`/… replaced by explicit raw parameters
  (`u : VelocityField`, `p : PressureField`, `f : VelocityField`, `K : Set Space`, `M D : ℝ`, …) and every `PacketAPI`/`PacketEnergyAPI` clause the fields rely on carried as an explicit
  hypothesis field or parameter (document the mapping in a table). Every declaration `[propext, Classical.choice, Quot.sound]`.

## Goal
1. `formalization/NSFormalization/Section3/T15/Scaling.lean` (namespace `NSFormalization.Section3.T15`): `structure PlacementData` and `structure ScalingAPI` restated over raw packet
   fields (all fields of the Spec, docstrings and paper lines kept), using lane 362's canonical rescaling definitions and T13's canonical `LocalizationAPI`; plus `def scalingStatement : Prop`
   in the same shape as the Spec's statement with the packet replaced by raw fields + hypotheses.
2. Probe `research/T15/probes/scaling_canonical.lean` (`cd verification && lake env lean …`): import `Contracts.V1.Packet`, `Contracts.V1.PacketImport`, the Spec's structures restated
   token-for-token (namespace only), and the conversions Spec → canonical (`ofSpec : ScalingAPI P place → T15.ScalingAPI (raw fields of P) …`) and canonical → Spec (given the raw
   hypotheses assembled into a `PacketImportAPI ν`), fieldwise, both directions where the field types are defeq (structure exception; say which fields need a `rfl` bridge to the
   canonical rescaling definitions and prove them).
3. Records: `research/T15/ATTEMPTS_UCAN.md` (the field-mapping table raw ↔ `PacketAPI`), `research/T15/axioms_ucan.lean`, status in `research/T15/T15_SPLIT.md` (add a U-CAN entry),
   report `research/T15/REPORT_384.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Scaling` (0 errors), `lake env lean` on the module (0 output), on the probe and axioms file; `make check`.

## Report
Commit on your branch; end with four parts (what is restated, with field counts and the mapping table / files / gaps / commands and results). Also write it to `research/T15/REPORT_384.md`.
