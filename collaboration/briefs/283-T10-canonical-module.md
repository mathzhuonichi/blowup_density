# Lane 283-T10-canonical-module — the canonical Lake module for the T10 periodic data layer (definitions only)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/283-T10-canonical-module` (git branch `erenup/283-T10-canonical-module`, based on
`origin/erenup/integration-section3`). Read `CLAUDE.md` (contract import rules; the "结构体例外" paragraph; Lean environment), then
`research/T10/Spec.lean` (the reconciled T10 specification, **including lead amendment 1** — see `research/T10/RECONCILIATION.md` §5 and the
amended `IsPeriodicDatum` / `IsPeriodicHomogeneousDatum` / `parseval_forward`), `research/T10/COMPARISON.md`, `collaboration/SECTION3_PLAN.md` §2
(representation decision (b): physical layer = unit-periodic fields on ℝ³, analysis on the coefficient side `lp (Fin 3 → ℤ) 2`, D01-style datum
architecture), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`. New files only; no edits to existing modules. `formalization/` must **never** import `Contracts.*` or
  `Bindings.*` (dependency direction is `verification → formalization`).
- Definitions must be **token-for-token** the spec's (same names, same argument order, same bodies), so that the future contract can restate them and
  bridge by `rfl`. Where the spec restates an existing local declaration verbatim (it says so in docstrings: `NSFormalization.Paper1.torusLift`,
  `periodicFourierCoeff`, `PeriodicTorus`, `PeriodicFrequency`, `periodicTorusMeasure` from `formalization/NSFormalization/Paper1/TorusCube.lean`),
  **import and reuse** that declaration instead of duplicating it, and record the identification in the module docstring.

## Goal
Create `formalization/NSFormalization/Section3/T10/PeriodicData.lean` (namespace `NSFormalization.Section3.T10`) containing every declaration of
`research/T10/Spec.lean` **except** the `TorusDataAPI` structure: the periodicity predicates, coefficient carriers (`PeriodicScalarData`,
`PeriodicVectorData`, `realPeriodicSubmodule`, `PeriodicSobolev`), data predicates and extended norms (`IsPeriodicDatum`, `periodicSobolevENorm`,
mean/mean-zero objects, homogeneous datum/norm, derivative symbol, solenoidal/Leray/reweight predicates), paths and force norms, classes,
pressure gauge, `ClassicalSolutionT`, lifespan/breakdown/density objects, energy norms. The vocabulary the spec takes from `Contracts.V1.Data`
(`SpatialField`, `SpaceTimeField`, `SpaceTimeScalar`, `coordinateVector`, `IsSobolevPath`, `ClassicalSolutionR`, …) must come from its **local
canonical source**: find each one through the `rfl` bridges in `verification/Bindings/Data.lean` and the `CONTRACT_CANONICAL_MODULES` list in
`experiments/check_contracts.py`; for `ClassicalSolutionR` the single allowed local restatement is `Section4/A02/Restrict.lean` §0 (import it; do
not copy). If the spec's `ClassicalSolutionT` mentions a `ClassicalSolutionR` field, keep the same field types so a later fieldwise conversion is
defeq. State in `research/T10/CANONICAL.md` a table `Spec.lean:line → module declaration → source of each imported name`.

## Deliverables
1. The module above; `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PeriodicData` succeeds (silent apart from
   replayed upstream warnings); `lake env lean` on it prints nothing. If Lake does not pick up the new `Section3` directory, report the exact
   error and how `Section4` modules are rooted in `formalization/lakefile.toml` — do not edit the lakefile without saying so.
2. Probe `research/T10/probes/api_on_canonical.lean` (checked with `cd verification && lake env lean ../research/T10/probes/api_on_canonical.lean`):
   imports the new module (and `Contracts.V1.Data` if needed for vocabulary) and restates the **amended** `TorusDataAPI` structure over the
   module's declarations, verbatim from `Spec.lean:429-end` with only the namespace changed. It must elaborate; this is the statement the T10 proof
   lanes will prove. Also include `example : (NSFormalization.Section3.T10.torusLift : (Space → Space) → _) = NSFormalization.Paper1.torusLift := rfl`
   style checks for every reused declaration (or say why a check is not applicable).
3. `research/T10/CANONICAL.md` (the mapping table + the list of declarations that were reused rather than copied), `research/T10/ATTEMPTS_CANONICAL.md`
   (anything that failed, exact error text), report `research/T10/REPORT_283.md`.

## Gates
`lake build` of the module, `lake env lean` on the module and the probe (0 output), `make check` from the worktree root.

## Report
Commit on your branch (`[283-T10] canonical periodic data module`); end with four parts (what the module defines / files / gaps with error text /
commands and results).
