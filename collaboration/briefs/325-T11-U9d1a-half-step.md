# Lane 325-T11-U9d1a-half-step — T11 U9d1-analytic: discharge `TorusHalfStepInput` (real-order convolution bound, fractional heat smoothing, Duhamel endpoint continuity)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/325-T11-U9d1a-half-step` (git branch `erenup/325-T11-U9d1a-half-step`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,LocalExistenceProbe,LocalExistence,ConvolutionBound,GalileanClasses,PhysicalRecovery,Rescaling,Uniqueness,MeanIdentity,Persistence}.lean` (lane 319's `Persistence.lean` defines the target `TorusHalfStepInput` and proves the half-order ladder and `torusForcedMildOn_persistence` from it; lane 317's `ConvolutionBound.lean` has the order-3 convolution bound; lane 311/313's heat lemmas `torusHeatSmoothing_norm_le` (σ = 1), `torusHeatCLM`, `torusSmoothingCLM`, `torusSmoothingKernel_integrable`), `Section3/T10/{FourierCalculus,ForcePaths}.lean`, `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean` (`reweightDatum` at real orders), the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/half_step_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Sub-unit **U9d1-analytic** (`research/T11/EXISTENCE_ROUTE.md` §"U9d1 status — lane 319"): **discharge lane 319's single named input `TorusHalfStepInput`** (read its exact statement and
docstring in `Section3/T11/Persistence.lean`: for the forced mild solution `u` of order 3 and any continuous order-`r` realization `v` (`r ≥ 3`, `IsPeriodicReweight 3 r (u t) (v t)`), produce a
continuous order-`(r + 1/2)` realization `w` on `Ico 0 T` with `IsPeriodicReweight r (r+1/2) (v t) (w t)` — one half-order gain, interval including `0`, same `T`). Three analytic pieces, then assembly:
(a) **real-order convolution bound** `Q : H^r × H^r → H^{r-1}` for real `r ≥ 3` — generalize lane 317's `ConvolutionBound.lean` (Peetre `W(k)^{(r-1)/2} ≤ 2^{(r-1)/2}(W(k')^{(r-1)/2} + W(k−k')^{(r-1)/2})`,
Cauchy–Schwarz, lattice summability of `W^{-3/2 - ε}`… follow the same proof with `reweightDatum`); (b) **fractional heat smoothing** `‖e^{νtΔ}‖_{H^s → H^{s+3/2}} ≤ C (νt)^{-3/4}`: the symbol bound
`W(k)^{3/4} e^{-νt·4π²|k|²} ≤ C (νt)^{-3/4}` for `t > 0` (`x^{3/4} e^{-x}` bounded; note `W = 1 + 4π²|k|²`, handle the `+1` — the bound holds with a constant depending on `T` for `t ≤ T`, say so) — generalize
`torusHeatSmoothing_norm_le` (σ = 1) to σ = 3/2, and the kernel integrability `∫₀ᵗ (ν(t−s))^{-3/4} ds < ∞`; (c) **Duhamel with endpoint continuity**: `w(t) := e^{νtΔ}A' + ∫₀ᵗ e^{ν(t−s)Δ}(P(s) − Q(v(s),v(s))) ds`
where `A'` is the all-order datum of the smooth `a` reweighted to order `r+1/2` (`CriterionBridge.exists_periodicDatum_smooth`), the integrand continuous in `s` with values in `H^{r-1}` (by (a) and
`ContinuousOn v`) and the kernel integrable (by (b)) ⇒ `w` continuous on `Ico 0 T` with values in `H^{r+1/2}` (dominated convergence / `intervalIntegral` continuity in the upper limit with an integrable
singular kernel — Mathlib: `intervalIntegral.continuousOn_primitive_interval`-type lemmas, or prove continuity by hand with the `ε`-split of the kernel), and `IsPeriodicReweight r (r+1/2) (v t) (w t)`
coefficientwise from the mild equation `TorusForcedMildOn` (the two Duhamel formulas have the same coefficients since the heat/convection symbols commute with the reweighting). Then
`theorem torusHalfStepInput : TorusHalfStepInput` and the corollaries `persistence_halfOrder_ladder torusHalfStepInput`, `torusForcedMildOn_persistence torusHalfStepInput` instantiated
(`persistence_unconditional`). **Peeling rule**: if exactly one of (a)/(b)/(c) is out of reach, name it as the single input with its exact statement and prove the rest; do not stop at definitions. (L, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/HalfStep.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_half_step.lean`.
2. Records `research/T11/ATTEMPTS_HALF_STEP.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_325.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.HalfStep` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[325-T11] HalfStep`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
