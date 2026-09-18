# Lane 308-T11-U1-flow-conversion — T11 U1 — `ClassicalSolutionT ↔ Paper1.PeriodicLifespan.Flow` fieldwise conversion (structure exception)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/308-T11-U1-flow-conversion` (git branch `erenup/308-T11-U1-flow-conversion`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/flow_conversion_roundtrip.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U1** of `T11_SPLIT.md` §1, design in §4: `toFlow (w : ClassicalSolutionT ν a f T) : Paper1.PeriodicLifespan.Flow ν a f T` (11 of 14 fields transfer; the two spelling lemmas
`Source.residual ν u p t x = NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x` (`rfl`) and `IsPeriodicOn I z ↔ UnitSpatialPeriodsOn I z` (`Iff.rfl`) — verify these first, they are
the whole point), `ofFlow (U : Flow ν a f T) (hs : …) (hg : …) (hn : PressureGaugeT (Ico 0 T) U.pressure) : ClassicalSolutionT ν a f T` taking the three extra fields (`sobolev`, `pressure_gradient`,
`pressure_gauge`) as parameters with their exact types, round-trip lemmas (`toFlow_ofFlow`, `ofFlow_toFlow` on the data fields by `rfl`/`Flow.ext`), and the force-class transport
`MemForceT f → IsSmoothPeriodicForce f` (one direction, as §4 says). Also export `lifespan_eq`-style helpers if the split lists them under U1. No named input expected.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/FlowConversion.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_flow_conversion.lean`.
2. Records `research/T11/ATTEMPTS_FLOW_CONVERSION.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_308.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.FlowConversion` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[308-T11] FlowConversion`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
