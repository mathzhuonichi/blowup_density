# Lane 328-T11-U9d1a-real-order-convolution — T11 U9d1a — real-order convolution bound: `Q : H^r × H^r → H^{r−1}` for every real `r ≥ 3`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/328-T11-U9d1a-real-order-convolution` (git branch `erenup/328-T11-U9d1a-real-order-convolution`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/convolution_bound_real_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Prove the real-order generalization of lane 317's order-3 bound: for every real `r ≥ 3` there is a bounded real bilinear map `torusConvolutionCLM_real r : PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev (r − 1)`
whose coefficients are the projected convection symbol `torusProjectedConvectionSymbol` (transported to order `r` by `IsPeriodicReweight` — state the coefficient identity precisely, in the
`.1 i k` form with the correct weights, and prove it), with an explicit norm bound `‖torusConvolutionCLM_real r‖ ≤ torusConvolutionConstant_real r`. Route: copy `ConvolutionBound.lean`'s proof
(discrete Young/Cauchy–Schwarz with the Peetre inequality `W(k)^{s} ≤ 2^{s}(W(k')^{s} + W(k−k')^{s})` for `s = (r−1)/2 ≥ 1` — prove Peetre for real exponents via `Real.rpow` monotonicity and
`(a+b)^s ≤ 2^{s-1}(a^s+b^s)`… or the simpler `max` bound) with the lattice summability of `W^{-3/2-ε}` (already used at order 3). Also export the reweighting-compatibility lemma: for `r ≤ r'`,
the order-`r'` map restricted to reweighted data agrees coefficientwise with the order-`r` map. Non-vacuity: two constant-mode data. (L, sol preferred; astra only as fallback.)
## No named input (binding for this lane)
This lane must prove its theorem **outright**. Do not introduce any `def … : Prop` input, alias, or structure that packages the goal or a part of it; do not restate the goal under another name.
If a sub-step defeats you, deliver every lemma you did prove, and write in `REPORT` §3 the exact statement you could not prove and the exact Lean error/obstacle — an honest partial delivery is
acceptable, a stub or alias is discarded without review.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_convolution_bound_real.lean`.
2. Records `research/T11/ATTEMPTS_CONVOLUTION_BOUND_REAL.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_328.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ConvolutionBoundReal` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[328-T11] ConvolutionBoundReal`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
