# Lane 316-T11-U7-mean-identity — T11 U7 — mean identity (`mean_formula`, `mean_derivative`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/316-T11-U7-mean-identity` (git branch `erenup/316-T11-U7-mean-identity`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/mean_identity_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U7** of `T11_SPLIT.md` §1: the two fields of `PeriodicMeanReductionAPI` verbatim from `research/T11/probes/api_on_canonical.lean`: `mean_formula` (`velocityMeanT w.velocity t = galileanMeanT a f t`
on `Ico 0 T`) and `mean_derivative` (`HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t` on `Ioo 0 T`). Route: integrate `w.momentum` over `T³`; `meanT (Δu) = meanT (∇p) = meanT (convectionDivergenceT u) = 0`
(each is a periodic derivative, mean zero by `integral_torusLift` + periodicity — `Section3/T10/FourierCalculus.lean`'s derivative symbol at `k = 0`, or a direct FTC-per-coordinate argument);
differentiate under the Haar integral as in `Paper1/PeriodicPressureNormalization.lean:149` (`pressureMean_hasDerivAt_interior`), vector version; then `mean_formula` by FTC from `mean_derivative`
+ the initial value (`w.initial`) with `galileanMeanT a f t = meanT a + ∫₀ᵗ meanT (f s)` (`Section3/T11/LocalTheory.lean`). No named input expected. (L, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/MeanIdentity.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_mean_identity.lean`.
2. Records `research/T11/ATTEMPTS_MEAN_IDENTITY.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_316.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MeanIdentity` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[316-T11] MeanIdentity`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
