# Lane 484-T23-U5-domain-comparison — T23 U5: registered T22 domain / zero-extension comparison (`domain_zeroExt_comparison` + the domain norm definitions and copied norm API transport)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/484-T23-U5-domain-comparison` (git branch `erenup/484-T23-U5-domain-comparison`, = lane 480's branch (T23 U-CAN, in review) + `origin/erenup/integration-section3` with 476/477/478 merged). Read `CLAUDE.md`, **`research/T23/T23_SPLIT.md`** (§0; your unit verbatim; §2; §4), `research/T23/SPEC_ISSUES.md` (G0, G1), `research/T23/Spec.lean` (the exact field statements), `Section3/T23/Boundary.lean` (lane 480: canonical `BoundaryInsertionAPI` 48 fields, `boundaryInsertionStatement`/`'`, geometry lemmas), `Placement.lean` (476), `LocalCorrection.lean` + `SpatialExtension.lean` + `LocalCorrectionBridge.lean` + `StatementRepair.lean` (477), `DomainSolution.lean` + `NoSlipEnergy.lean` + `DifferenceEnergy.lean` + `BoxIntegration.lean` (478), `research/T23/REPORT_{476,477,478b,480}.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first (`lake build NSFormalization.Section3.T23.Boundary` and the modules you consume).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only under `formalization/NSFormalization/Section3/T23/` (your own module names below) and `research/T23/`. Never import `Paper1/BoundaryCorollary.lean`.
- **Parallel lanes**: U2b (481), U3 (482), U4 (483), U5 (484), U6 (485), U8 (486) run at the same time on the same base. Do not create another lane's module; where you need another lane's result, **thread it as an explicit hypothesis** (state your theorems over the needed fields/facts as parameters, exactly as the T21 lanes 472/474 did) — the assembly lane (U9) discharges them. Never restate a record that `Section3/T23/Boundary.lean`, `Placement.lean`, `LocalCorrection.lean` or `DomainSolution.lean` already provides.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file. **Commit a module skeleton within 15 minutes and after each closed lemma.**

## Goal
Exactly `T23_SPLIT.md` U5: apply the registered T22 theorem (`verification/Contracts/V1/BoundedDomainNorm.lean:109` through its canonical implementation `Section3/T22/ZeroExtensionComparison.lean:28` and `OrderZero.lean:219`) to the **difference** `zε(t)` on `Ω` with the fixed compact `K = closure B`; choose `C` once per `s` before `t` and `ε`; integrate both inequalities over `Ioi 0` with `ENNReal` lintegral monotonicity (infinite norms stay valid); the domain norm definitions `Spec:615,622,629,640,648` and the copied norm API `:289,304,324` transported to the canonical vocabulary (`rfl` bridges where valid). Thread U3's force smoothness and U4's fixed support as hypotheses.

Deliverables: your module(s) (`Section3/T23/DomainNorms.lean, Section3/T23/DomainComparison.lean`), a probe `research/T23/probes/T23-U5-domain-comparison_closes.lean` (each field by `exact` against `Boundary.lean`/`Spec.lean`, instantiated at the threaded hypotheses), `research/T23/axioms_T23-U5-domain-comparison.lean`, `research/T23/ATTEMPTS_T23-U5-domain-comparison.md`, status line in `T23_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build <each new module>` (0 errors), `lake env lean` on each (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (statements / files / gaps with error text / commands and results). Also write it to `research/T23/REPORT_484.md`.
