# Lane 310-T11-U3-galilean-classes — T11 U3 — Galilean class and translation algebra (`translation_preserves_sobolev`, `transformed_classes`, `transformed_mean_zero`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/310-T11-U3-galilean-classes` (git branch `erenup/310-T11-U3-galilean-classes`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/LocalTheory.lean`, `Section3/T12/*.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/galilean_classes_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U3** of `T11_SPLIT.md` §1: the three fields of `PeriodicMeanReductionAPI` listed there, verbatim from `research/T11/probes/api_on_canonical.lean`:
`translation_preserves_sobolev` (datum case: translating by `y` multiplies coefficients by the unimodular `exp(2πi k·y)` — use `Section3/T10` lemmas (`periodic_shift_int`, `torusLift_apply_of_periodic`,
`integral_torusLift`, Haar translation invariance on `UnitAddTorus`) — so the datum norm is unchanged; `⊤` case: translate back by `-y`), `transformed_classes` (`meanZeroPartT a ∈ initialClassT`,
`galileanForceT a f ∈ forceClassT`: smoothness of `forceMeanT f`, `galileanMeanT`, `galileanShiftT` — the vector analogue of `cubeIntegral_contDiffOn_Ico` (`Paper1/PeriodicPressureNormalization.lean:93`) —,
periodicity, divergence-free, compact positive-time support inherited from `f`), `transformed_mean_zero`. No named input expected.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/GalileanClasses.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_galilean_classes.lean`.
2. Records `research/T11/ATTEMPTS_GALILEAN_CLASSES.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_310.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.GalileanClasses` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[310-T11] GalileanClasses`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
