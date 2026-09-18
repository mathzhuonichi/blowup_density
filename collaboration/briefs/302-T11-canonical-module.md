# Lane 302-T11-canonical-module — the canonical Lake module for the T11 vocabulary (definitions only)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/302-T11-canonical-module` (git branch `erenup/302-T11-canonical-module`, based on `origin/erenup/integration-section3`, which contains the canonical
T10 module `formalization/NSFormalization/Section3/T10/PeriodicData.lean` (incl. the solution-class declarations `IsPeriodicSobolevPath`, `forceSobolevENormT`, `initialClassT`, `MemForceT`,
`PressureGaugeT`, `normalizePressureT`, `ClassicalSolutionT`, `maximalLifespanT`, `RegularThroughT`, `breakdownSetT`, …), the T12/T13 modules, and the registered contract `T01.torus_data`).
Read `CLAUDE.md` (contract import rules; Lean environment; the "结构体例外" paragraph), the precedents `research/T10/CANONICAL.md`, `research/T12/CANONICAL.md`, `research/T13/CANONICAL.md`
(how lanes 283/297/299 built canonical modules and probes), then the reconciled T11 specification `research/T11/Spec.lean` (binding: `research/T11/RECONCILIATION.md` §0–§3),
`research/T11/COMPARISON.md`, and the top 40 lines of `logs/LESSONS.md` (**every `instance`/`local instance` gets an explicit unique name**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`. New files only; no edits to existing modules. `formalization/` must never import `Contracts.*`/`Bindings.*`.
- Definitions must be **token-for-token** the spec's (same names, argument order, bodies) so the future contract can restate them and bridge by `rfl`. T10 vocabulary
  (including `ClassicalSolutionT` and the solution-class defs) is **imported** from `NSFormalization.Section3.T10.PeriodicData` (never copied). Where a T11 declaration is token-identical to a
  registered Section 4 one (`convectionDivergence`, `SolvesBelow`, `IsMaximalSolution`, `squaredHTwoIntegral` in `Contracts/V2/{LocalTheory,Continuation}.lean`), import and reuse its
  **local canonical source** (find it through the `rfl` bridges in `verification/Bindings/LocalTheoryV2.lean`, `Bindings/ContinuationV2.lean`) if the source is a `def` on the same
  vocabulary; otherwise define the torus version and record why reuse is impossible.

## Goal
Create `formalization/NSFormalization/Section3/T11/LocalTheory.lean` (namespace `NSFormalization.Section3.T11`) containing every **new** declaration of `research/T11/Spec.lean`
(`IsPeriodicSobolevPathOn`, `convectionDivergenceT`, `scalarSpatialLaplacianT`, `SolvesBelowT`, `IsMaximalPeriodicSolution`, `timeShiftT`, `ExtendsBeyondT`, `galileanMeanT` and the
Galilean transforms, the viscosity rescaling maps, and whatever else the spec defines) — **except** the five API structures (`PeriodicLocalRegularity` is a `Prop` structure *on a solution*:
include it only if the reconciliation treats it as vocabulary consumed by the APIs; otherwise leave it to the probe, and say which). Record in `research/T11/CANONICAL.md` a table
`Spec.lean:line → module declaration → source of each imported name`.

## Deliverables
1. The module; `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.LocalTheory` succeeds; `lake env lean` on it prints nothing.
2. Probe `research/T11/probes/api_on_canonical.lean` (`cd verification && lake env lean ../research/T11/probes/api_on_canonical.lean`): imports the module (+ T10's, + contracts for vocabulary
   checks) and restates all five API structures over the modules' declarations, verbatim from `Spec.lean` with only namespaces changed. It must elaborate; this is the statement the T11
   proof lanes will prove. Include `example … := rfl` checks for every reused declaration.
3. `research/T11/CANONICAL.md`, `research/T11/ATTEMPTS_CANONICAL.md` (exact error text of anything that failed), report `research/T11/REPORT_302.md`; additionally a short survey
   `research/T11/IMPLEMENTATION_CANDIDATES.md`: for each API field, the closest existing declaration in `formalization/NSFormalization/Paper1/Periodic*.lean` (e.g. `PeriodicOrdinaryLocal`,
   `PeriodicLifespan*`, `PeriodicInitialData`, `PeriodicPressureFlowBridge`) or `vendor/HeliCorgi/Formal/*` with file:line and the gap between its statement and the field (this is
   the input for splitting the T11 proof lanes; grep, do not guess).

## Gates
`lake build` of the module, `lake env lean` on module and probe (0 output), `make check` from the worktree root.

## Report
Commit on your branch (`[302-T11] canonical local theory module`); end with four parts (what the module defines / files / gaps with error text / commands and results).
