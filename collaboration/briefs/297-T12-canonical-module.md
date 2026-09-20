# Lane 297-T12-canonical-module — the canonical Lake module for the T12 vocabulary (definitions only)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/297-T12-canonical-module` (git branch `erenup/297-T12-canonical-module`, based on `origin/erenup/integration-section3`, which contains
the canonical T10 module `formalization/NSFormalization/Section3/T10/PeriodicData.lean` and the registered contract `T01.torus_data`). Read `CLAUDE.md` (contract import rules;
Lean environment), the precedent `research/T10/CANONICAL.md` + `research/T10/REPORT_283.md` (how lane 283 built the T10 canonical module and its probe), then the reconciled T12
specification `research/T12/Spec.lean` (with `research/T12/RECONCILIATION.md` §0–§3 binding), `research/T12/COMPARISON.md`, and the top 40 lines of `logs/LESSONS.md`
(in particular the 2026-09-17 lesson: **every `instance`/`local instance` gets an explicit unique name**; shared instances live once in the canonical module).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`. New files only; no edits to existing modules. `formalization/` must never import `Contracts.*`/`Bindings.*`.
- Definitions must be **token-for-token** the spec's (same names, argument order, bodies) so the future contract can restate them and bridge by `rfl`.
  T10 vocabulary is **imported** from `NSFormalization.Section3.T10.PeriodicData` (never copied). Where the spec's declaration is token-identical to a registered Section 4
  definition (`lift`, `gradientTensor`, `laplacian` of `Contracts/V1/GradientL6.lean`), import and reuse its **local canonical source** (find it through the `rfl` bridges in
  `verification/Bindings/GradientL6.lean`) instead of duplicating, and record the identification.

## Goal
Create `formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean` (namespace `NSFormalization.Section3.T12`) containing every **new** declaration of
`research/T12/Spec.lean` (the ones not copied from T10): the scalar datum pair (`IsPeriodicScalarDatum`, `periodicScalarSobolevENorm`, with the integrability conjunct),
`periodicLpENorm`, `SmoothPeriodicT`/`MemPeriodicHomogeneous`-type predicates, `IsPeriodicLambda`, and whatever else the spec defines before `MeanZeroSobolevCalculusAPI` —
**except** the API structure itself. Record in `research/T12/CANONICAL.md` a table `Spec.lean:line → module declaration → source of each imported name`.

## Deliverables
1. The module; `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.MeanZeroCalculus` succeeds; `lake env lean` on it prints nothing.
2. Probe `research/T12/probes/api_on_canonical.lean` (`cd verification && lake env lean ../research/T12/probes/api_on_canonical.lean`): imports the new module (+ T10's) and
   restates the **Type-valued** `MeanZeroSobolevCalculusAPI` structure over the modules' declarations, verbatim from `Spec.lean` with only namespaces changed (constants as data
   fields first, then the nine clauses). It must elaborate; this is the statement the T12 proof lanes will prove. Include `example … := rfl` checks for every reused declaration.
3. `research/T12/CANONICAL.md`, `research/T12/ATTEMPTS_CANONICAL.md` (exact error text of anything that failed), report `research/T12/REPORT_297.md`.

## Gates
`lake build` of the module, `lake env lean` on module and probe (0 output), `make check` from the worktree root.

## Report
Commit on your branch (`[297-T12] canonical mean-zero calculus module`); end with four parts (what the module defines / files / gaps with error text / commands and results).
