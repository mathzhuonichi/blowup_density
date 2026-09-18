# Lane 381-T20-canonical — T20 `prop:critical`: the canonical module restating the reconciled `CriticalRegularityTAPI` over the canonical T10/T11/T12 modules, with the probe and the H¹-ball check

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/381-T20-canonical` (git branch `erenup/381-T20-canonical`, based on `origin/erenup/integration-section3` after #338).
Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T20/Spec.lean` (the reconciled statement, merged in #296: `CriticalRegularityTAPI` at `:1015` and its statement, on top of copied
T10/T11/T12 vocabulary blocks)**, `research/T20/RECONCILIATION.md`, `research/T20/COMPARISON.md`, the canonical modules `Section3/T10/*.lean`, `Section3/T11/{LocalTheory,Assembly,…}.lean`
(the registered `T01.torus_local_theory` vocabulary lives in `formalization/` as these modules), `Section3/T12/{MeanZeroCalculus,SpectralGap,FourierEmbeddings,TameProduct}.lean`,
the existing canonical-module lanes as templates (`Section3/T13/Localization.lean` + `research/T13/probes/api_on_canonical.lean`; `Section3/T16/LocalPotential.lean` +
`research/T16/probes/api_on_canonical.lean` — the fieldwise-conversion pattern for structures), **`research/T11/H1_GAP.md`** (the H¹-ball narrowing of the registered continuation API),
and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; no proofs of the API fields (this lane is the canonical *statement* module + probe, no theorem about the fields); no edits to existing
  modules; new files only. **No stubs**: every restated definition/field is the Spec's text (only the namespace and the imported canonical names change).
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]` (there are only `def`s/`structure`s and `rfl`/conversion lemmas here).

## Goal
1. New module `formalization/NSFormalization/Section3/T20/CriticalRegularity.lean` (namespace `NSFormalization.Section3.T20`): restate over the canonical vocabulary (import
   `Section3/T10`, `Section3/T11`, `Section3/T12` modules; never copy a T10/T11/T12 definition that exists canonically — use it by name) the T20-specific definitions of
   `research/T20/Spec.lean` and `structure CriticalRegularityTAPI` (all fields verbatim, docstrings with paper lines kept), plus the statement `def`. Where the Spec's copied T11 APIs
   (`PeriodicLocalTheoryAPI`, `PeriodicContinuationAPI`, `PeriodicMeanReductionAPI`) are consumed as parameters/fields, use the canonical `Section3/T11/Assembly.lean` structures
   (note the registered continuation API is the **H³-narrowed** `PeriodicContinuationH3API`; if `CriticalRegularityTAPI` takes the manuscript `PeriodicContinuationAPI`, keep the Spec's
   spelling in the module (restate that structure verbatim if it is not canonical) — do not silently narrow; record the fact in the H¹ check).
2. Probe `research/T20/probes/api_on_canonical.lean` (`cd verification && lake env lean ../research/T20/probes/api_on_canonical.lean`): restate the Spec's T20 definitions and
   `CriticalRegularityTAPI` **token-for-token** (namespace only), prove each restated `def` equals the module's by `rfl`, and give the fieldwise conversions Spec ↔ module for the
   structure (structure exception; both directions), plus a `def`-level non-vacuity note (no inhabitant is constructed — statement lane).
3. **`research/T20/H1_CHECK.md`**: list every field/definition of the Spec that mentions `periodicSobolevENorm 1` (`grep -n`; e.g. `Spec.lean:402,437`) and, for each, state whether the
   proof will need the H¹-ball restart (`PeriodicRestartH1` — the named unproved manuscript predicate of `T01.torus_local_theory`) or whether the H³-narrowed `PeriodicContinuationH3API`
   / the ball-free `extendsBeyond`/criterion fields suffice (cite `research/T11/H1_GAP.md` §3's consumer analysis). Do not change the Spec; report the finding.
4. Records: `research/T20/ATTEMPTS_CANONICAL.md`, conformance `research/T20/axioms_canonical.lean`, status in `research/T20/COMPARISON.md`, report `research/T20/REPORT_381.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.CriticalRegularity` (0 errors), `lake env lean` on the module (0 output), on the probe and axioms file;
`make check`.

## Report
Commit on your branch; end with four parts (what is restated, with field counts / files / the H¹ check findings / commands and results). Also write it to `research/T20/REPORT_381.md`.
