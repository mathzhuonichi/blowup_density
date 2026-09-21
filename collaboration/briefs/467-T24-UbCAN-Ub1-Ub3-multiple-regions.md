# Lane 467-T24-UbCAN-Ub1-Ub3-multiple-regions — T24b: canonical `MultipleRegionsAPI` record + Ub1 (placement/scaling selection), Ub2 (components), Ub3 (single-copy supports)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/467-T24-UbCAN-Ub1-Ub3-multiple-regions` (git branch `erenup/467-T24-UbCAN-Ub1-Ub3-multiple-regions`, = `origin/erenup/integration-section3` with **T15 complete**: `Section3/T15/*` incl.
`Assembly.lean` (lane 459: `placementData … T hT` template with explicit horizon, `scalingAPI` over the raw packet clauses, `scalingStatement_holds`), `Scaling.lean` (raw-field `PlacementData u p f K` :106 and `ScalingAPI` 21 fields :106-460),
`Placement.lean`, `SingleCopy.lean` (`*_singleCopy`), `Solution.lean` (`solution`), `Blowup.lean`, `Energy.lean`; registered `T02.scaling` (`Contracts/V1/Scaling3.lean`)).
Read `CLAUDE.md`, **`research/T24/T24_SPLIT.md`** (§0 — especially the T24b canonical-threading paragraph at `:38-45` and the finding "T24b does NOT consume T18"; §1 T24b units Ub1/Ub2/Ub3 verbatim; §2 ledger), `research/T24/Spec.lean:1140-1340`
(`finiteVelocitySum/PressureSum/ForceSum :1144`, `MultipleRegionsAPI :1176-1333` — 30 fields, `Type`, over `P : PacketImportAPI ν`, `T`, `N`, `regionCenter regionRadius`; `multipleRegionsStatement :1335`), `research/T24/RECONCILIATION.md` (T24b rulings),
the canonical affine/conservative records already in `Section3/T24/{AffineFamily,AffineAssembly,ConservativeAssembly}.lean` (how lanes restated `Prop`/`Type` records canonically over raw fields and bridged to the Spec), `research/T24/REPORT_{392,430}.md`
(registration pattern), `research/T15/REPORT_459.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T15.Assembly NSFormalization.Section3.T15.Solution NSFormalization.Section3.T15.SingleCopy`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
1. **U-CAN**: `formalization/NSFormalization/Section3/T24/Multiple.lean` (namespace `NSFormalization.Section3.T24`): the canonical `MultipleRegionsAPI` (30 fields, `Type`) restated token-for-token from `research/T24/Spec.lean:1176-1333` over the
   **canonical raw-field** T15 records (`NSFormalization.Section3.T15.PlacementData u p f K`, `ScalingAPI …` — thread the packet as raw fields `u p f K M E` + the raw clauses exactly as `Section3/T18/Assembly.lean`'s `InsertionData` does for T18, since
   `formalization/` cannot import `Contracts.*`), plus `multipleRegionsStatement` in the canonical shape, and a probe `research/T24/probes/multiple_api_on_canonical.lean` checking field-by-field agreement with the Spec record (the Spec's
   `PacketImportAPI`-indexed spelling vs the raw-field canonical one: state the bridge as `example`s over the projections, as lane 457 did for T19). Docstrings cite paper lines (`03-torus.tex:668-740`).
2. **Ub1** (`placement`, `placement_time`, `placement_chart`, `scaling`, `ε`, `eps_admissible`, `eps_time`): for each region `j`, a `PlacementData` with `chartCenter := regionCenter j`, `chartRadius := regionRadius j` (`chartBall_in_cube` from the API's
   `region_interior` hypothesis field), `T := T`, `x₀ := regionCenter j`, `Kstar`/`ε₀` as in lane 459's `placementData` (copy the construction, do not import its fixed centre); `scaling j := scalingAPI …` at that placement; `ε j ∈ Ioc 0 (place j).ε₀` with
   `(ε j)^2 < T` (`eps_time`).
3. **Ub2** (`component`, `component_pin`): `(scaling j).solution (ε j) …` selects `S_j : ClassicalSolutionT ν 0 F_{ε j} T` with velocity/pressure pins.
4. **Ub3** (`component_support`, `component_force_support`): on `fundamentalCube`, single-copy (`velocity_singleCopy`/`force_singleCopy`) + `eps_space` + `placement_chart` put `x₀ + ε•K_*` inside the region ball, so both vanish on `Q ∖ B_j`.
Deliver these as theorems/defs over the threaded data (a structure `RegionsData` bundling `N`, `regionCenter`, `regionRadius`, the raw packet + clauses, `T`, `hT`, and the `region_*` hypotheses is the natural carrier — mirror `InsertionData`), each
with the exact field statement. Deliverables: the module(s), the probe, `research/T24/axioms_ub1_ub3.lean`, `research/T24/ATTEMPTS_UB1_UB3.md`, status lines (U-CAN, Ub1, Ub2, Ub3) in `T24_SPLIT.md`. Ub4–Ub7 are later lanes: do not start them, but
record in the ATTEMPTS file anything you learn that they need (e.g. which disjointness lemma shape Ub4 will want).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.Multiple` (0 errors; plus any further new module), `lake env lean` on each new module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (statements / files / gaps with error text / commands and results). Also write it to `research/T24/REPORT_467.md`.
