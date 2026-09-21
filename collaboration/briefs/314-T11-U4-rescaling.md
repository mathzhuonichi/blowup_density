# Lane 314-T11-U4-rescaling — T11 U4 — viscosity algebra (`inverse_identities`, `scaled_classes`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/314-T11-U4-rescaling` (git branch `erenup/314-T11-U4-rescaling`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/rescaling_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U4** of `T11_SPLIT.md` §1: the two algebraic fields of `PeriodicViscosityRescalingAPI` verbatim from `research/T11/probes/api_on_canonical.lean`: `inverse_identities` (three `funext`
+ positive-`ν` algebra on `unitViscosity*T`/`restoreViscosity*T` of `Section3/T11/LocalTheory.lean`) and `scaled_classes` (`unitViscosityInitialT ν a ∈ initialClassT`, `unitViscosityForceT ν f ∈ forceClassT`:
smoothness/periodicity/divergence-free are preserved by the linear rescaling; time dilation maps a compact subset of `Ioi 0` to one). No named input expected. (S, sol.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/Rescaling.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_rescaling.lean`.
2. Records `research/T11/ATTEMPTS_RESCALING.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_314.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Rescaling` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[314-T11] Rescaling`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
