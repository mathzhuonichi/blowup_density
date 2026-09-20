# Lane 299-T13-canonical-module — the canonical Lake module for the T13 vocabulary (definitions only)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/299-T13-canonical-module` (git branch `erenup/299-T13-canonical-module`, based on `origin/erenup/integration-section3`, which contains the canonical
T10 module `formalization/NSFormalization/Section3/T10/PeriodicData.lean`, the T12 module `Section3/T12/MeanZeroCalculus.lean`, and the registered contract `T01.torus_data`).
Read `CLAUDE.md` (contract import rules; Lean environment), the precedents `research/T10/CANONICAL.md`, `research/T12/CANONICAL.md` + `research/T12/REPORT_297.md` (how lanes 283/297
built canonical modules and their probes), then the reconciled T13 specification `research/T13/Spec.lean` (binding: `research/T13/RECONCILIATION.md`), `research/T13/COMPARISON.md`,
and the top 40 lines of `logs/LESSONS.md` (in particular: **every `instance`/`local instance` gets an explicit unique name**; shared instances live once in the canonical module —
if you need the torus-measure probability instance, take it from `Section3/T10/Parseval.lean`'s `periodicTorusMeasure_probability` or wait for lane 296's named instance; do not add another anonymous one).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`. New files only; no edits to existing modules. `formalization/` must never import `Contracts.*`/`Bindings.*`.
- Definitions must be **token-for-token** the spec's (same names, argument order, bodies) so the future contract can restate them and bridge by `rfl`.
  T10 vocabulary is **imported** from `NSFormalization.Section3.T10.PeriodicData` (never copied). Where a T13 declaration restates a Section 4 D01 object (the ℝ³ homogeneous
  norm `dotHomogeneousENorm`, `IsHomogeneousDatum`, …), import and reuse its **local canonical source** (find it through the `rfl` bridges in `verification/Bindings/HomogeneousNorm.lean`
  and `Bindings/Data.lean`-family files) instead of duplicating, and record the identification.

## Goal
Create `formalization/NSFormalization/Section3/T13/Localization.lean` (namespace `NSFormalization.Section3.T13`) containing every **new** declaration of `research/T13/Spec.lean`
(the fixed fundamental cube, coordinate-ball support predicate, lattice periodization `periodize`, the singular kernel `K_s`, `cFrac`/the constant `c_s`, the lattice tail, the
whole-space and torus Gagliardo difference integrals `I_R`/`I_T`, the physical gradient norm, …) — **except** the `LocalizationAPI` structure itself. Record in
`research/T13/CANONICAL.md` a table `Spec.lean:line → module declaration → source of each imported name`.

## Deliverables
1. The module; `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.Localization` succeeds; `lake env lean` on it prints nothing.
2. Probe `research/T13/probes/api_on_canonical.lean` (`cd verification && lake env lean ../research/T13/probes/api_on_canonical.lean`): imports the new module (+ T10's, + `Contracts.V1.*`
   for vocabulary if needed) and restates `LocalizationAPI` (six fields) over the modules' declarations, verbatim from `Spec.lean` with only namespaces changed. It must elaborate; this is the
   statement the T13 proof lanes will prove. Include `example … := rfl` checks for every reused declaration.
3. `research/T13/CANONICAL.md`, `research/T13/ATTEMPTS_CANONICAL.md` (exact error text of anything that failed), report `research/T13/REPORT_299.md`.

## Gates
`lake build` of the module, `lake env lean` on module and probe (0 output), `make check` from the worktree root.

## Report
Commit on your branch (`[299-T13] canonical localization module`); end with four parts (what the module defines / files / gaps with error text / commands and results).
