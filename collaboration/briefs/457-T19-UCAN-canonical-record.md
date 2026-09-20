# Lane 457-T19-UCAN-canonical-record — T19 U-CAN: canonical restatement of the four T19 records (`PeriodicDensityAPI`, `MixedRegionAPI`, `StrongClosureAPI`, `ProjectionAPI`) in `Section3/T19/Density.lean`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **statement** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/457-T19-UCAN-canonical-record` (git branch `erenup/457-T19-UCAN-canonical-record`, based on `origin/erenup/integration-section3`). Today the four T19
structures exist only in `research/T19/Spec.lean` (`:192 PeriodicDensityAPI`, `:265 MixedRegionAPI`, `:340 StrongClosureAPI`, `:456 ProjectionAPI`, all `Prop`, 13 fields total, over the **registered**
`Contracts/V1/TorusLocalTheory.lean` vocabulary — `ClassicalSolutionT`, `breakdownSetT`, `RelativelyDenseT`, `forceClassT`, `initialClassT`, `forceSobolevENormT`, `criticalOrder`, … — plus copied T18
vocabulary where `prop:density` consumes `thm:insertion`); `Section3/T19/Bookkeeping.lean` (lane 388) proves the six U1–U6 fields as free-standing theorems over the canonical T10/T11 vocabulary but
declares no record. `formalization/` cannot import `Contracts.*`, so the canonical proofs of T19 U7–U14 and of T21 need canonical records, exactly as T20 has `Section3/T20/CriticalRegularity.lean`
(lane 381) and T17 has `Section3/T17/Correction.lean` (lane 394). Read `CLAUDE.md`, `research/T19/Spec.lean` (all four structures with docstrings and the `…Statement` defs), `research/T19/RECONCILIATION.md`
(§0 lead approval: bases B/B/A/A, all `Prop`, T18 **not** threaded, `RelativelyDenseT`, registered `alpha`, no honesty guards), `research/T19/T19_SPLIT.md` (which unit consumes which field; U7–U14 consume
the T18 insertion — check how the Spec phrases that: through `periodicInsertionStatement`-level facts or through a threaded record), the precedents `Section3/T20/CriticalRegularity.lean` (canonical
restatement + `criticalRegularityStatement`, and `research/T20/probes/api_on_canonical.lean`-style probes) and `research/T17/probes/correction_canonical.lean` (fieldwise Spec ↔ canonical conversions),
`Section3/T19/Bookkeeping.lean` (the six proved fields — their exact statements must be the canonical fields' types), `Bindings/TorusLocalTheory.lean` (`maximalLifespanT_eq`, `toContract`/`ofContract`
conversions for the `ClassicalSolutionT` structure exception), `research/T21/RECONCILIATION.md` §0 point 6 (this module is the "eventual fix" for T21's copied T19 block), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- Statements only for the four records (no field proofs — those are the T19 units); no placeholder/`True` fields; no edits to existing modules; new files only. The field list and the field texts must be
  the Spec's, with only the vocabulary renamed to the canonical `NSFormalization.Section3.T10/T11` spellings (and T18's canonical `Section3/T18/*` records where the Spec threads T18). Every conversion
  in the probe must be `rfl` or a fieldwise conversion (no `sorry`); every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Deliverables
1. `formalization/NSFormalization/Section3/T19/Density.lean` (namespace `NSFormalization.Section3.T19`): the four structures restated canonically with docstrings citing paper lines + the four
   `…Statement : Prop` defs; a section "already proved" showing by `example` that each of the six lane-388 theorems has literally the corresponding field's type (so U-REG can assemble them by name).
2. `research/T19/probes/api_on_canonical.lean`: the Spec ↔ canonical fieldwise conversions in both directions for all four records (in the Contracts vocabulary, importing `Contracts.V1.*` and the Spec),
   with `rfl` drift checks for every renamed notion (`maximalLifespanT` needs `Bindings.TorusLocalTheory.maximalLifespanT_eq`, not `rfl` — say so).
3. `research/T19/ATTEMPTS_UCAN.md`, `research/T19/axioms_ucan.lean`, U-CAN status line in `T19_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Density` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (what was restated and what the six examples check / files / any field that could not be restated canonically and why / commands and results). Also write it to `research/T19/REPORT_457.md`.
