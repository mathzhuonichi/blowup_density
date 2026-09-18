# Lane 422-T18-U1-insertion-data — T18 U1: the inserted triple, the three `eq:insertion` formulas, the threshold and the trivial hypothesis fields

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/422-T18-U1-insertion-data` (git branch `erenup/422-T18-U1-insertion-data`, based on `origin/erenup/integration-section3`, which contains
the canonical prerequisites: lane 384's raw-field `PlacementData`/`ScalingAPI` (`Section3/T15/Scaling.lean`), lane 394's canonical 45-field `CorrectionAPI` (`Section3/T17/Correction.lean`,
over `PlacementData` and the canonical T13/T16 records), the T11 canonical modules (`Section3/T11/*`, registered as `T01.torus_local_theory`), and `Section3/T16/{LocalPotential,Assembly}.lean`).
Read `CLAUDE.md`, **`research/T18/T18_SPLIT.md` §0 (the lead note: `formalization/` cannot import `Contracts.V1.PacketAPI`, so the canonical T18 module takes the raw-field records) and
unit U1** (`:59-68`), `research/T18/Spec.lean:1660-1740` (the fields `velocity`/`pressure`/`force` data (`:1700-1704`), `velocity_formula` (`:1710`), `pressure_formula` (`:1723`),
`force_formula` (`:1732`), `ε₀` (`:1684`), `eps_pos`, `eps_le_scaling`, `eps_le_cutoff`, `delta_pos`, `reference_force_mem`, `initial_mem`), `research/T18/RECONCILIATION.md` §2
(threading: `PacketImportAPI`/`PlacementData`/`ScalingAPI`/`reference`/`CorrectionAPI`), `research/T15/REPORT_384.md`, `research/T17/REPORT_394.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder `Prop` fields; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only (except the registry/work-items additions named below).
- No named inputs. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T18/Insertion.lean` (namespace `NSFormalization.Section3.T18`): the **canonical U1 layer** of the insertion. First restate the
parameters of `PeriodicInsertionAPI` that U1 needs in canonical form (a `structure InsertionData` bundling the raw-field `PlacementData`, the `ScalingAPI` record, the reference
classical solution data (`v, π, g` with the T11 hypotheses the Spec threads), the `CorrectionAPI` record and `normalizePressureT`), then `def velocity ε z := v z + w_ε z + U_ε z`,
`pressure ε := normalizePressureT (fun z ↦ π z + P_ε z)`, `force ε z := g z + H_ε z + F_ε z` (read the exact Spec spellings of `w_ε, U_ε, P_ε, H_ε, F_ε` from the threaded records),
the three `*_formula` theorems (by `rfl`), `ε₀ := min place.ε₀ D.ε₀` with `eps_pos`, `eps_le_scaling`, `eps_le_cutoff`, and `delta_pos`, `reference_force_mem`, `initial_mem`
(each the corresponding conjunct of the threaded records). Every theorem's type must be the Spec field's type with the Spec parameters replaced by the canonical bundle's projections —
write a probe `research/T18/probes/insertion_closes.lean` with the Spec-form fields discharged from the canonical ones (fieldwise conversions as in lane 394's
`research/T17/probes/correction_canonical.lean`). Deliverables: the module, the probe (+ a non-vacuity instance if a concrete `PlacementData`/reference witness exists in the tree —
grep the T15/T17 probes; else state exactly what witness is missing), `research/T18/axioms_u1.lean`, `research/T18/ATTEMPTS_U1.md`, U1 status line in `T18_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.Insertion` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T18/REPORT_422.md`.
