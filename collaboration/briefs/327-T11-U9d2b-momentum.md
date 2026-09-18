# Lane 327-T11-U9d2b-momentum — T11 U9d2b — Duhamel time differentiation: time smoothness of the coefficient paths and the momentum equation of the physical velocity

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/327-T11-U9d2b-momentum` (git branch `erenup/327-T11-U9d2b-momentum`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,LocalExistenceProbe,LocalExistence,ConvolutionBound,GalileanClasses,PhysicalRecovery,Rescaling,Uniqueness,MeanIdentity,Persistence,ClassicalAssembly}.lean` (lane 320's `ClassicalAssembly.lean`: `PersistenceInput T u` — all-order continuous realizations of the mild solution — and from it the physical velocity's spatial smoothness `persistence_physical_spatial_smooth` and divergence-freeness `persistence_physical_divergence`; lane 318's `torusPhysicalVelocity`; lane 313's `TorusForcedMildOn`, Duhamel formula, heat CLMs; lane 317's convection bound; read `research/T11/EXISTENCE_ROUTE.md` §"U9d2 status — lane 320"), `Section3/T10/{FourierCalculus,ForcePaths}.lean` (derivative/Laplacian symbols, inversion), `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/mild_momentum_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Sub-unit **U9d2b** of U9d2 (`EXISTENCE_ROUTE.md` §"U9d2 status — lane 320": Duhamel time differentiation and the momentum equation are missing). **Single allowed named input**:
`PersistenceInput T u` exactly as in lane 320's `ClassicalAssembly.lean`. Under the U9d hypotheses and `PersistenceInput T u`, prove: (i) **time differentiability of the coefficient paths**: for every
order `m`, the continuous realization `u_m` of `PersistenceInput` is differentiable on `Ioo 0 T` (and one-sided at `0` if you can) with `d/dt û(t)(k) = −ν·4π²|k|²·û(t)(k) + (P̂(F(t) − Q(u(t),u(t))))(k)` —
from the Duhamel formula `TorusForcedMildOn` (differentiate `e^{νtΔ}A` via the heat symbol and the integral term via the FTC with a continuous integrand: `torusHeat_add`/coherence,
`intervalIntegral.integral_hasDerivAt_right`, the heat CLM's strong continuity `torusHeatCLM_continuous`); state it as `HasDerivAt (fun t ↦ u_m t) … t` in `PeriodicSobolev m` (or coefficientwise —
say which, and give both if cheap); (ii) **time smoothness of the physical velocity**: `torusPhysicalVelocity u` is `ContDiffOn ℝ ∞ … (Ioo 0 T ×ˢ univ)` (or the joint regularity field `ClassicalSolutionT`
demands — read `Section3/T10/PeriodicData.lean` for the exact field; derive from (i) iterated: the derivative of the coefficient path is again a path of the same type, so induct on the order of the
time derivative using the rapid decay), plus continuity up to `t = 0`; (iii) **momentum equation**: the field `w.momentum` of `ClassicalSolutionT` in its exact form (`∂ₜu − νΔu + (u·∇)u + ∇p = g`
with the pressure of lane 326 — if lane 326 has not landed, take its `mildPressure` with the datum identity `∇p̂ = (I−P)(F − Q)` as part of the same single input? **No**: keep exactly one input —
prove (i)+(ii) unconditionally on `PersistenceInput`, and state (iii) as `momentum_of_pressure`: for any pressure `p` whose gradient datum is `(I−P)(F−Q)` the momentum equation holds — then lane 326's
pressure instantiates it). Use `FourierCalculus.lean` symbols for `Δ`, `∇`, the convection identity `(u·∇)u = ∇·(u⊗u)` under `divergence` (`LocalTheory.convectionDivergenceT`, `Section4/A01/ConvectionDivergence`),
and `Leray.lean` for `P̂`. **Peeling rule**: at most ONE further named input, stated exactly; record in `EXISTENCE_ROUTE.md` §"U9d2b status" (append only). (L, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/MildMomentum.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_mild_momentum.lean`.
2. Records `research/T11/ATTEMPTS_MILD_MOMENTUM.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_327.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildMomentum` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[327-T11] MildMomentum`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
