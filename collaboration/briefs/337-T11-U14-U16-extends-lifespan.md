# Lane 337-T11-U14-U16-extends-lifespan — T11 U14 + U16: `extendsBeyond` and `lifespanInfiniteOfLocallyFinite`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/337-T11-U14-U16-extends-lifespan` (git branch `erenup/337-T11-U14-U16-extends-lifespan`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,Restart,RestartBeyond,Maximal,Uniqueness,CriterionBridge,HighOrder}.lean` (lane 332's `RestartBeyond.lean`: `restartBeyond` and the exported `glueClassicalSolutionT` with agreement on `[0,T)`, `restrictClassicalSolutionT`, `solvesBelowT_of_classicalSolutionT`; lane 323's `Maximal.lean`: `maximalLifespanT_eq_lifespan`, `exists_maximal`, `maximal_unique`; lane 322's `HighOrder.lean`: `higherOrderBound_of_energyInequality` (the field follows from `hRhigh`, being discharged by lanes 335/336); lane 309's `CriterionBridge.lean`), `Section3/T10/PeriodicData.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/extends_beyond_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Units **U14** and **U16** of `T11_SPLIT.md` §1: the fields `extendsBeyond` and `lifespanInfiniteOfLocallyFinite` of `PeriodicContinuationAPI`, verbatim from `research/T11/probes/api_on_canonical.lean`.
Inputs: the **single allowed named input** `PeriodicQuantitativeLocalInput'` (as in lanes 321/332), and — because U12's `higherOrderBound` is still being closed (lanes 335/336) — take the
**`higherOrderBound` field statement itself as an explicit theorem hypothesis** (copy its exact statement from the probe as a binder `(hHigh : …)`; not a `def … : Prop`), so your results are
`extendsBeyond_of_input (H : PeriodicQuantitativeLocalInput') (hHigh : <higherOrderBound statement>) : <extendsBeyond statement>` and likewise for `lifespanInfiniteOfLocallyFinite`.
Route (U14): from `SolvesBelowT ν a f S u p` with `squaredHTwoIntegralT S u ≠ ⊤` (`CriterionBridge.lean` bridges the criterion), apply `hHigh` at `m = 1` on each `[0, b]`, `b < S`, to get a
uniform `H¹` trajectory bound `K` on `[0, S)` (the bound does not degrade as `b ↑ S` — check the field's exact form; the constant is the endpoint constant), then lane 332's `restartBeyond` gives the
concrete `ClassicalSolutionT ν a f (S + δ)` agreeing with `(u, p)` on `[0, S)`, which **is** `ExtendsBeyondT ν a f S u p` (`Section3/T11/LocalTheory.lean`) — strictly stronger than the registered `A04.extendsBeyond`.
Route (U16): contrapose — if `maximalLifespanT ν a f = L ≠ ⊤`, the hypothesis at `S = L.toReal` (the `≤` is load-bearing, `RECONCILIATION.md` §2) with lane 323's maximal solution as the `SolvesBelowT`
pair (`solvesBelowT_of_classicalSolutionT` on every horizon below `L`) and U14 gives a solution on `L.toReal + δ`, hence `ofReal (L.toReal + δ) ≤ L` by `horizon_le_lifespan`, absurd. Also
export `lifespan_ge_of_extends`. No other input; honest partial with the exact obstacle if stuck. (M, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/ExtendsBeyond.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_extends_beyond.lean`.
2. Records `research/T11/ATTEMPTS_EXTENDS_BEYOND.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_337.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ExtendsBeyond` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[337-T11] ExtendsBeyond`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
