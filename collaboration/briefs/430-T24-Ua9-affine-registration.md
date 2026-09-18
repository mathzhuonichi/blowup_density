# Lane 430-T24-Ua9-affine-registration — T24a Ua9: assemble `AffineVariationAPI` (13 fields) over the raw packet clauses, `affineVariationStatement`, and register `T04.affine_variation`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/430-T24-Ua9-affine-registration` (git branch `erenup/430-T24-Ua9-affine-registration`, based on `origin/erenup/integration-section3`, which contains
all T24a unit modules: `Section3/T24/{AffineBasics (392: radius_pos, window, zero_initial, late_agreement, distinct), AffineDivergence (402), AffineMomentum (398), AffineSpeed (403), AffineEnergy (407),
AffineForce (414), AffineWitness + AffineFamily (417), AffineNonisolated (424)}.lean` and their probes `research/T24/probes/affine_*_closes.lean` (each discharging one registered-vocabulary field on
`Bindings.packet ν hν`)). Read `CLAUDE.md` (contract import rules: `Contracts/*` import only `Mathlib`/`Contracts.*` + the whitelist in `experiments/check_contracts.py`; restated definitions bridged
by `rfl` in `Bindings/`; `ensure_ascii=False, indent=2`; frozen V1 files untouched), **`research/T24/T24_SPLIT.md` §0 and unit Ua9** (`:150-153`) and §2 ledger, `research/T24/Spec.lean:940-1122`
(`AffineVariationAPI` with its 13 fields, its parameters `(ν) (P : PacketAPI ν) (c r τ₀ τ₁)` or however it is parameterised — read it — and `affineVariationStatement :1117`), `research/T24/RECONCILIATION.md`
(T24a is proved over raw packet clauses; the canonical assembly consumes the registered `I01.packet` witness at the contract level), all `research/T24/REPORT_{392,398,402,403,407,414,417,424}.md`
(§1 of each lists the exact raw clauses and geometric hypotheses each theorem takes — e.g. `force_support` needs only `0 < τ₀`, `speed_unbounded` needs `τ₁ < 1`, `energy_finite` needs the raw
`energyENorm 1 U < ⊤` which the registered `PacketAPI` does **not** carry as a field: derive it from `square_integrable`/`energy_isLUB`/`dissipation_integrable`/`dissipation_eq` as `ATTEMPTS_UA6.md`
sketches, in the Bindings layer), the registration precedents `verification/Contracts/V1/Packet.lean`/`Bindings/Packet.lean` (the `I01.packet` witness `Bindings.packet ν hν`), `Contracts/V1/Localization.lean`
+ `Bindings/Localization.lean` + `Tests/Localization.lean` (lane 371), `verification/contracts.json`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder fields; no edits to existing modules (new files only, plus the registry/work-items additions). Every restated definition bridged by `rfl`;
  every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Deliverables
1. `formalization/NSFormalization/Section3/T24/AffineAssembly.lean`: a canonical record type `AffineVariationCanonical` (or the Spec's structure restated over raw clauses — read how lanes
   398/402/… phrase their hypotheses and choose the bundle `structure AffineRawData` carrying `U P F ν c r τ₀ τ₁` and the raw packet clauses actually consumed), assembled from the eight unit modules
   (13 fields: `radius_pos`, `window`, `zero_initial`, `late_agreement`, `distinct`, `divergence_free`, `momentum`, `force_smooth`, `force_support`, `speed_unbounded`, `energy_finite`,
   `infinite_dimensional`, `nonisolated` — check the Spec's exact list and order).
2. `verification/Contracts/V1/AffineVariation.lean`: `AffineVariationAPI` **token-for-token from `research/T24/Spec.lean`** over the registered `Contracts/V1/Packet.lean`/`Data.lean` vocabulary
   (import; restate verbatim only what is unregistered — `affineCylinder`, `AffineAdmissible`, `affineVelocity`, `affinePressure`, `crossAdvection`, `affineForce`, `ckSeminormE`, … with provenance
   comments), and `affineVariationStatement` (`:1117`).
3. `verification/Bindings/AffineVariation.lean`: `rfl` bridges for every restated definition to `NSFormalization.Section3.T24.*`; the instance `affineVariation (ν) (hν) … : AffineVariationAPI …`
   built on `Bindings.packet ν hν` (derive the raw clauses from the packet fields, incl. the `energyENorm 1 velocity < ⊤` derivation), and `affineVariationStatement_holds`.
4. `verification/Tests/AffineVariation.lean`: `checkedAffineVariation`, `run_cmd TestSupport.checkAxioms`, a conformance `example` restating one field against `Spec.lean`, non-vacuity
   (`b = 0` admissible and the nonzero `AffineWitness.curlBump` instance).
5. Registry entry `T04.affine_variation` (`version: 1`, `parent_task` per the T24 work item, honest `scope`), `ensure_ascii=False, indent=2`, additions only — note lanes 423 (`T04.bounded_domain_norm`)
   and 427 (`T01.mean_zero_calculus`) are adding entries concurrently; keep yours a clean list-element addition so the lead can merge; `collaboration/work_items.json` + `python3 experiments/tasks.py render`.
   Records `research/T24/ATTEMPTS_UA9.md`, `research/T24/axioms_ua9.lean`, Ua9 status in `T24_SPLIT.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts` = base + 1, `base_compatibility_checked: true`);
the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Try `research/T24/REPORT_430.md`; if the report-file guard blocks it, put the full report in your final message.
