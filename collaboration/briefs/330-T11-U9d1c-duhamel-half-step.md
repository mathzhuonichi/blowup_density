# Lane 330-T11-U9d1c-duhamel-half-step — T11 U9d1c — Duhamel endpoint continuity and the half-step: `theorem torusHalfStepInput : TorusHalfStepInput`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/330-T11-U9d1c-duhamel-half-step` (git branch `erenup/330-T11-U9d1c-duhamel-half-step`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,LocalExistenceProbe,LocalExistence,ConvolutionBound,Persistence,ClassicalAssembly}.lean` (lane 317's `ConvolutionBound.lean`: the order-3 discrete weighted convolution bound `torusScalarConvectionLp_norm_le`, `torusConvolutionCLM`; lanes 311/313: `torusHeatSymbol`, `torusHeatSmoothing_norm_le` (σ = 1), `torusHeatCLM`, `torusSmoothingCLM`, `torusSmoothingKernel_integrable`; lane 319's `Persistence.lean`: the target `TorusHalfStepInput` and the reweighting lemmas), `Section3/T12/SpectralGap.lean` (`reweightDatum` at real orders, weight comparisons), `Section3/T10/{PeriodicData,Leray}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Peeling rule suspended for this lane — see 'No named input' below.** (Original text kept for context:) Satisfiability / peeling rule (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/duhamel_half_step_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Base includes lanes 328 (`ConvolutionBoundReal.lean`) and 329 (`FractionalSmoothing.lean`) — check `ls Section3/T11/`. Prove **`theorem torusHalfStepInput : TorusHalfStepInput`** (statement in
`Persistence.lean`; read its docstring): given the forced mild solution `u` of order 3 and a continuous order-`r` realization `v` on `Ico 0 T` (`r ≥ 3`), build `w(t) := e^{νtΔ}A' + ∫₀ᵗ e^{ν(t−τ)Δ}(P(τ) − Q_r(v(τ),v(τ))) dτ`
at order `r + 1/2`, where `A'` is the order-`(r+1/2)` datum of the smooth `a` (`CriterionBridge.exists_periodicDatum_smooth`), `Q_r` is lane 328's map at order `r` (values in `H^{r−1}`), and the
integrand is transported to order `r+1/2` by lane 329's smoothing (gain `3/2`, kernel `(ν(t−τ))^{-3/4}`); prove: (i) the Bochner integral exists on `Ico 0 T` (integrand continuous in `τ` on `[0,t)`
with an integrable singular bound — `MeasureTheory.Integrable` via `IntegrableOn.mono` of the kernel times a continuous bound), (ii) `w` is continuous on `Ico 0 T` (the ε-split argument: near
`τ = t` the kernel integral is small; away from it the integrand is jointly continuous — or Mathlib's dominated-convergence continuity `continuousOn_of_dominated`), (iii)
`IsPeriodicReweight r (r+1/2) (v t) (w t)` for `t ∈ Ico 0 T`: coefficientwise both `w` and `v` equal the Duhamel formula of `TorusForcedMildOn` (the heat, convection and integral coefficients commute
with the reweighting — use lane 313's `TorusForcedMildOn` unfolding and the coefficient identities of 328/329), so `w t` is the order-`(r+1/2)` reweight of `v t`. Then instantiate lane 319's
`persistence_halfOrder_ladder`/`torusForcedMildOn_persistence` with it (`persistence_unconditional`). Non-vacuity: the constant-datum family. (L, sol preferred; astra fallback.)
## No named input (binding for this lane)
This lane must prove its theorem **outright**. Do not introduce any `def … : Prop` input, alias, or structure that packages the goal or a part of it; do not restate the goal under another name.
If a sub-step defeats you, deliver every lemma you did prove, and write in `REPORT` §3 the exact statement you could not prove and the exact Lean error/obstacle — an honest partial delivery is
acceptable, a stub or alias is discarded without review.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_duhamel_half_step.lean`.
2. Records `research/T11/ATTEMPTS_DUHAMEL_HALF_STEP.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_330.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.DuhamelHalfStep` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[330-T11] DuhamelHalfStep`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
