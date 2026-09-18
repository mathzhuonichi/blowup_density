# Lane 396-T12-U4-velocity-critical-l3 — T12 U4: `velocityCriticalL3` verbatim (mean-zero `Ḣ^{1/2}(T³) ↪ L³(T³)`) from the cutoff–Gagliardo core, the Haar↔cube transfer, the registered A05 whole-space embedding and the spectral gap

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/396-T12-U4-velocity-critical-l3` (git branch `erenup/396-T12-U4-velocity-critical-l3`, based on lane 377's branch merged with
`origin/erenup/integration-section3`: `Section3/T12/{MeanZeroCalculus,SpectralGap,FourierEmbeddings,TameProduct,Cutoff,HaarCube,CutoffGagliardo}.lean` — lane 377's
`cutoff_gagliardo_half` (+ `cutoffGagliardoConst`), lane 366's `eLpNorm_torusLift_eq_restrict`/`periodicLpENorm_eq_restrict`/`eLpNorm_restrict_eq_of_tsupport`, lane 365's `cutoffMul`
(`= v` on the cube, `tsupport ⊆ interior largerCube`), `spectralGap` (`SpectralGap.lean:331`, `‖v‖_{L²} ≤ Cgap(s)·periodicHomogeneousENorm s v` for mean-zero `v`)).
Read `CLAUDE.md`, **`research/T12/T12_SPLIT.md` §0 and unit U4 (target verbatim `research/T12/probes/api_on_canonical.lean:148-151`, route)**, `research/T12/REPORT_{365,366,377}.md`,
the **registered** whole-space embedding `Section4/A05/CriticalL3.lean` (`velocityCriticalL3 :394`, constant `criticalL3Const :302`, hypothesis `MemHInfty`/datum shape — read it) and
its norm bridge `verification/Bindings/GradientL6V2.lean:44` (`gradientL6V2_dotHomogeneousENorm_eq`: A05's homogeneous norm = `Section4.D01.dotHomogeneousENorm`, the spelling of
`cutoff_gagliardo_half`), `paper/sections/appendix-b-embeddings.tex:20-31`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; the `mul_le_mul_*` renames).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T12/CriticalL3.lean` (namespace `NSFormalization.Section3.T12`): `theorem velocityCriticalL3` verbatim —
`∀ v : SpatialField, MemPeriodicHomogeneous (1/2) v → periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1/2) v` with an explicit positive
`CcriticalHalf` (`def` + `CcriticalHalf_pos`). Route (T12_SPLIT U4): `periodicLpENorm 3 v = eLpNorm (torusLift v) 3 Haar = eLpNorm v 3 (volume.restrict Q) = eLpNorm (cutoffMul v) 3 (restrict Q) ≤ eLpNorm (cutoffMul v) 3 volume`
(366 + `cutoffMul = v` on `Q`); the registered `A05.velocityCriticalL3` applied to `cutoffMul v` (smooth compactly supported ⇒ its `MemHInfty`/datum hypothesis — `Cutoff.lean`'s
`memHInfty_cutoffMul` if lane 365 provided it, else prove it from `Section4/D01` `exists_smoothL2Field_of_memHInfty`-type lemmas) gives `≤ criticalL3Const · dotHomogeneousENorm (1/2) (cutoffMul v)`
after the bridge `gradientL6V2_dotHomogeneousENorm_eq`; `cutoff_gagliardo_half` bounds that by `C(‖v‖_{L²(Q)} + periodicHomogeneousENorm (1/2) v)` for **smooth mean-zero** `v`; `spectralGap`
absorbs `‖v‖_{L²}`. The field quantifies over `MemPeriodicHomogeneous (1/2) v` (not necessarily smooth): read the definition in `MeanZeroCalculus.lean` — if it already implies smooth
periodic mean-zero (check), done; otherwise handle the general case by density/approximation only if the field genuinely requires it (state exactly what `MemPeriodicHomogeneous` gives and
prove the theorem under it; if a density argument is needed and heavy, deliver the smooth-mean-zero theorem `velocityCriticalL3_smooth` plus the exact residual for the general case).

## Deliverables
1. `Section3/T12/CriticalL3.lean`; 2. probe `research/T12/probes/critical_l3_closes.lean` (the API field closed by `exact`; non-vacuity on lane 377's `probeMZ`); 3. `research/T12/ATTEMPTS_U4.md`,
`research/T12/axioms_u4.lean`, status in `research/T12/T12_SPLIT.md` U4, report `research/T12/REPORT_396.md` (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.CriticalL3` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and the constant / files / gaps with exact error text / commands and results).
