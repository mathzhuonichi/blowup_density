# Lane 344-T13-constant-endpoints — T13 the fields `constant_pos_finite`, `endpoint_zero`, `endpoint_one` of `LocalizationAPI`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/344-T13-constant-endpoints` (git branch `erenup/344-T13-constant-endpoints`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T13/Localization.lean` (the T13 vocabulary: `fundamentalCube`, `SupportedInBall`, `latticeVector`, `periodize`, `fractionalRadialKernel`, `cFrac`, `periodicKernel`, `latticeTail`, `IReal`, `ITorus`, `gradientENorm`; read `research/T13/CANONICAL.md`), `Section3/T10/{PeriodicData,FourierCalculus,ForcePaths,Parseval,DatumBasics,PhysicalBridge}.lean`, `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, `Section3/T11/{ClassicalRegularity,PairingBound,MildPressure}.lean` (Bernstein bounds, lattice summability, periodic convolution theorem), `Section4/D01/{HomogeneousNorm,HomogeneousWitness}.lean` (the ℝ³ homogeneous norm `dotHomogeneousENorm` and its witnesses), and the target statements `research/T13/probes/api_on_canonical.lean` (`LocalizationAPI : Prop`, six fields; read every field's exact statement and docstring in `research/T13/Spec.lean`, the paper `03-torus.tex:22-98`, and `research/T13/COMPARISON.md` §"Proof dependencies"/"Needs a lemma"), the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T13/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T13/RECONCILIATION.md` and `research/T13/COMPARISON.md`**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T13/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T13/probes/constant_endpoints_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Prove three of the six fields of `research/T13/probes/api_on_canonical.lean` verbatim: (1) `constant_pos_finite` — the explicit Gagliardo constant `cFrac s` (read its definition in `Section3/T13/Localization.lean`: an integral of `(1 − cos(2π h·e))/|h|^{3+2s}`-type or as spelled) is positive and finite for `0 < s < 1` (convergence at `0` from `1 − cos ≤ |·|²`, at `∞` from `≤ 2`; positivity from a positive integrand on a positive-measure set; Mathlib: `MeasureTheory.integral_pos_iff_support_of_nonneg`, polar/spherical coordinates via `MeasureTheory.Measure.integral_comp_polarCoord` or a direct radial bound with `volume` of shells — say which); (2) `endpoint_zero` and (3) `endpoint_one` — the `s = 0` and `s = 1` endpoint equalities the spec states (read them: single-copy identities relating `IReal`/`ITorus` at the endpoints to the `L²`/gradient norms, or the equalities of the kernels/constants at the endpoints — follow the exact statement; the gradient identity uses `ForcePaths.gradientTensor_parseval` / `FourierCalculus.periodicFourierCoeff_gradient_sq`). **No named input**; honest partial with the exact obstacle if stuck (e.g. if an endpoint identity needs the full Gagliardo identity of lanes 345/346, say so exactly). (M–L, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean` (namespace `NSFormalization.Section3.T13`); the probe; conformance `research/T13/axioms_constant_endpoints.lean`.
2. Records `research/T13/ATTEMPTS_CONSTANT_ENDPOINTS.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T13/REPORT_344.md`; update your unit's row in
   `research/T13/COMPARISON.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.ConstantEndpoints` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[344-T11] ConstantEndpoints`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
