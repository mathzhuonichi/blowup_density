# Lane 434-T17-U9-energy-bound — T17 U9: torus energy bound `‖w_ε‖_{E_T} ≤ C ε^{3/2}` of the periodized correction + the two honest-slice `MemLp` fields

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/434-T17-U9-energy-bound` (git branch `erenup/434-T17-U9-energy-bound`, based on `origin/erenup/integration-section3`, which contains
`Section3/T17/{CorrectionProfile,Transport,LatticeDeriv,CorrectionDeriv,ForceDeriv,ForceProfile,Correction,ForceSupport}.lean` (lane 373's `Transport.lean`: the periodized correction
`D.correction ε` as a lattice lift of the single-copy `physicalCorrection`, `correction_eq`-type bridges; lane 385's derivative bounds), `Section3/T15/HaarBridge.lean` (U-TB1: `eLpNorm (torusLift
(periodize f)) 2 periodicTorusMeasure = eLpNorm f 2 volume` for `f` supported in the interior of the cube, and the `gradientENorm`/`energyGradientT` companion), `Section3/T16/LatticeLift.lean`,
`Section3/T10/PeriodicData.lean:330-341` (`energyEssSupT`/`energyGradientT`/`energyENormT`), and the registered Section 4 correction energy `Contracts/V1/Correction.lean` (`I02.correction_energy_bound`
and friends — grep `energy` there and in `Section4/I02/Energy.lean:103,140`)). Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U9** (`:204-213`), the canonical fields
`correction_slice_memLp`, `correction_gradient_memLp`, `energyConst`, `energyConst_nonneg`, `correction_energy_bound` in `Section3/T17/Correction.lean` (Spec form `research/T17/Spec.lean:896-920`),
`research/T17/REPORT_{373,385,425,431}.md` (431's `measure_torusPoint_image_le` and the Haar-vs-Lebesgue single-copy technique are on lane 431's branch, not on this base — re-derive what you need or
state it as a local lemma), `research/T15/REPORT_333.md` (HaarBridge), `research/T17/SPEC_ISSUES.md` (G1), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** Only the documented G1 `hv : ContDiff ℝ ∞ v` may appear as an extra premise (say where). An honest partial with the exact residual
  statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T17/Energy.lean` (namespace `NSFormalization.Section3.T17`): `def energyConst : ℝ` (explicit, nonnegative: `energyConst_nonneg`) and the three
theorems `correction_slice_memLp`, `correction_gradient_memLp`, `correction_energy_bound` with types literally the canonical fields at the concrete `correctionData` (probe by `exact` as lanes 425/431 do;
same premise block as 425 plus whatever the Euclidean energy bound needs). Route: each torus slice of `D.correction ε` is the periodization of the single-copy `physicalCorrection` slice, which is smooth
with compact support inside the cube (placement: `ε·θR < r < 1/2`), so `MemLp … 2 periodicTorusMeasure` follows from HaarBridge (`memLp_torusLift_*`) or from continuity + compactness on the torus;
`energyENormT place.T (D.correction ε) = Data.energyENorm place.T (physicalCorrection …)` by the single-copy Haar/Lebesgue energy bridge (HaarBridge U-TB1 for the `L²` slices and its gradient companion;
`essSup` over the same time interval), and the Euclidean side is the registered `I02.correction_energy_bound` (`Contracts/V1/Correction.lean` — read its exact statement, constants and hypotheses; go
through `Bindings` if the canonical `Section4/I02/Energy.lean` theorem is the one to apply) giving `≤ ofReal (C ε^{3/2})`. Set `energyConst := I02`'s constant (or the product of the bridge factors).
Deliverables: the module, `research/T17/probes/energy_closes.lean` (the three canonical fields closed by `exact`; instantiate at lane 425's constant-reference witness), `research/T17/axioms_u9.lean`,
`research/T17/ATTEMPTS_U9.md`, U9 status line in `T17_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Energy` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constant / files / gaps with error text / commands and results). Try `research/T17/REPORT_434.md`; if the report-file
guard blocks it, put the full report in your final message.
