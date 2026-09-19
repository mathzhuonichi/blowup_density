# Lane 439-T15-U4-U5-energy-mixed — T15 U4 (energy identities + honest slices) and U5 (mixed scaling + honest paths)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/439-T15-U4-U5-energy-mixed` (git branch `erenup/439-T15-U4-U5-energy-mixed`, based on `origin/erenup/integration-section3`, which contains
`Section3/T15/{Bridges,ParsevalZero,HaarBridge,Scaling,Placement,SingleCopy}.lean` — lane 421's `velocity/pressure/force_singleCopy` and summability, lane 333's HaarBridge U-TB1 (`eLpNorm_torusLift_periodize`,
`eLpNorm_torusLift_spatialGradient_periodize`, the `energyGradientT` companion), lane 384's canonical raw-field `PlacementData`/`ScalingAPI`, and the Section 4 scaling energy/mixed theorems
`Section4/I03/Energy.lean` (`:487 energyEssSup_scaled_eq`, `:304 energyGradient_scaled_eq`, `:211 eLpNorm_scaled_slice`), `Section4/I03/Mixed.lean` (`:104 mixedNorm_parabolicForce`) and
`verification/Bindings/Scaling.lean` (`:318 mixedLebesgueENorm_scaledForce`, `:658/667`)). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0, unit U4 (`:96-103`) and unit U5 (`:104-111`)**, the canonical
fields `energySlices_memLp`, `packetEnergyIdentity`, `packetDissipationIdentity`, `mixed_memLp`, `packetMixedScaling` in `Section3/T15/Scaling.lean` (Spec form `research/T15/Spec.lean:790-850`),
`research/T15/REPORT_{333,376,384,421}.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
Two new modules (namespace `NSFormalization.Section3.T15`): `Section3/T15/Energy.lean` (U4: `energySlices_memLp`, `packetEnergyIdentity` `= ε^{1/2}·M`, `packetDissipationIdentity` `= ε^{1/2}·D` with
`M = P.energyBound`, `D = P.dissipationBound` — read the exact canonical spellings) and `Section3/T15/Mixed.lean` (U5: `mixed_memLp`, `packetMixedScaling` `= ε^{alpha p q}·‖F‖`), types literally the
`ScalingAPI` fields over the raw-field `PlacementData` (probe by `exact`). Route: U3's single copy collapses each torus slice to the ℝ³ scaled slice on the cube; U-TB1 moves the Haar norm to Lebesgue
(`|Q| = 1`); then the Section 4 `I03` scaling identities (`energyEssSup_scaled_eq`, `energyGradient_scaled_eq`, `mixedLebesgueENorm_scaledForce`) give the exact scalings; `essSup`/`IsLUB` and the
endpoint-insensitive `Ioo`/`Ioc` handled as in I03; `MemLp` slices/paths from `I03/Energy.lean:211`, `I03/Mixed.lean:104`, transported by the Haar bridge. Deliverables: the two modules,
`research/T15/probes/energy_mixed_closes.lean` (fields by `exact` + the concrete geometric instance of `placement_closes.lean`), `research/T15/axioms_u4_u5.lean`, `research/T15/ATTEMPTS_U4_U5.md`,
status lines for U4/U5 in `T15_SPLIT.md`. If one field needs an I03 lemma stated on the wrong time interval, prove the transport and say so; do not weaken the field.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Energy NSFormalization.Section3.T15.Mixed` (0 errors), `lake env lean` on each module (0 output), the probe, the
axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Try `research/T15/REPORT_439.md`; if the report-file guard blocks it,
put the full report in your final message.
