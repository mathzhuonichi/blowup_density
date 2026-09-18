# Lane 329-T11-U9d1b-fractional-smoothing — T11 U9d1b — fractional heat smoothing: `‖e^{νtΔ}‖_{H^s → H^{s+3/2}} ≤ C (νt)^{-3/4}` on `(0, T]`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/329-T11-U9d1b-fractional-smoothing` (git branch `erenup/329-T11-U9d1b-fractional-smoothing`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/fractional_smoothing_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Prove the σ = 3/2 smoothing estimate for the coefficient heat semigroup `torusHeat`/`torusHeatCLM` (lane 311/313): for `ν > 0`, `0 < t ≤ T`, every real `s`, and every `A : PeriodicSobolev s`,
the reweighted datum `e^{νtΔ}A` at order `s + 3/2` exists (`IsPeriodicReweight s (s+3/2)` of the heat image) with `‖(e^{νtΔ}A)_{s+3/2}‖ ≤ C_T · (νt)^{-3/4} · ‖A‖_s`, from the symbol bound
`W(k)^{3/4} e^{−νt·4π²|k|²} ≤ C_T (νt)^{-3/4}` (`W = 1 + 4π²|k|²`; `x^{3/4}e^{-x} ≤ (3/4)^{3/4}e^{-3/4}` for `x ≥ 0` plus the `+1` handled by `W ≤ 1 + 4π²|k|²`, giving a constant depending on `T`
— compute it explicitly); package it as a bounded linear map `torusHeatSmoothingCLM_frac s t : PeriodicSobolev s →L[ℝ] PeriodicSobolev (s + 3/2)` with the coefficient identity, and prove the
kernel integrability `IntegrableOn (fun τ ↦ (ν τ)^{-3/4}) (Ioc 0 t)` and `∫₀ᵗ (ν(t−τ))^{-3/4} dτ = 4 t^{1/4} ν^{-3/4}`. Also prove strong continuity of `t ↦ torusHeatSmoothingCLM_frac s t A` on
`Ioc 0 T` (dominated convergence on coefficients). Reuse `torusHeatSmoothing_norm_le` (σ = 1) as the model. Non-vacuity: a single mode. (M–L, sol preferred; astra fallback.)
## No named input (binding for this lane)
This lane must prove its theorem **outright**. Do not introduce any `def … : Prop` input, alias, or structure that packages the goal or a part of it; do not restate the goal under another name.
If a sub-step defeats you, deliver every lemma you did prove, and write in `REPORT` §3 the exact statement you could not prove and the exact Lean error/obstacle — an honest partial delivery is
acceptable, a stub or alias is discarded without review.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/FractionalSmoothing.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_fractional_smoothing.lean`.
2. Records `research/T11/ATTEMPTS_FRACTIONAL_SMOOTHING.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_329.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.FractionalSmoothing` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[329-T11] FractionalSmoothing`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
