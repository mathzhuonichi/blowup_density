# Lane 388-T19-U1-6-bookkeeping — T19 wave 1: the six pure bookkeeping units U1–U6 of `research/T19/T19_SPLIT.md` (`thresholdValue`, `mixedRegionArithmetic`, `regionExamples`, `energyTimeEmbedding`, `referenceFiniteEnergy`, zero-norm helpers)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/388-T19-U1-6-bookkeeping` (git branch `erenup/388-T19-U1-6-bookkeeping`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T19/T19_SPLIT.md` §0 and units U1–U6 (targets, inputs with file:line, routes)**, `research/T19/Spec.lean` (the four `Prop` structures — the targets
are its fields verbatim), `research/T19/RECONCILIATION.md` §3, the registered vocabulary (`Contracts/V1/TorusLocalTheory.lean`, `MainThresholds.lean`, `Data.lean`: `criticalOrder`,
`alpha`, the energy/mixed/Sobolev norms) and their canonical `formalization/` sources (`Section3/T10`, `Section3/T11`; `formalization/` cannot import `Contracts.*` — state the theorems over the
canonical modules and close the Spec's fields in the probe), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T19/Bookkeeping.lean` (namespace `NSFormalization.Section3.T19`; create the T19 canonical vocabulary you need — copy the Spec's
T19-specific defs verbatim, import everything canonical) with one theorem per unit U1–U6 in the exact field spelling: `thresholdValue` (`criticalOrder 1 = 1/2`), `mixedRegionArithmetic`
(`3/p + 2/q > 3 → 0 < alpha p q ∧ 0 < alpha p q + 1` — check the Spec's exact form and the registered `alpha`), `regionExamples` (`0 < alpha 2 1 ∧ 0 < alpha (4/3) 2`), `energyTimeEmbedding`
(`‖z‖_{L²_tL²} ≤ √T ‖z‖_{L^∞_tL²}` in the Spec's torus norm spellings — the `spaceTimeL2L2ENormT`/`energyENormT` route of the split), `referenceFiniteEnergy` (the Spec's field), and the
U6 zero-norm helpers (`forceSobolevENormT 1 s 0 = 0`, etc., as the split lists them, consumed by the density fields). Probe `research/T19/probes/bookkeeping_closes.lean` importing
`Contracts.*` and closing each Spec field by `exact` (with the `rfl` bridges to the registered names).

## Deliverables
1. `Section3/T19/Bookkeeping.lean`; 2. the probe (each field closed; numeric instances for the arithmetic fields); 3. `research/T19/ATTEMPTS_U1_6.md`, `research/T19/axioms_u1_6.lean`,
status in `research/T19/T19_SPLIT.md` U1–U6, report `research/T19/REPORT_388.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Bookkeeping` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T19/REPORT_388.md`.
