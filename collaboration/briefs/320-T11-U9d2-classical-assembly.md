# Lane 320-T11-U9d2-classical-assembly — T11 U9d2 — classical assembly: physical velocity/pressure, momentum equation, `ClassicalSolutionT` + `PeriodicLocalRegularity` from an all-order coefficient solution

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/320-T11-U9d2-classical-assembly` (git branch `erenup/320-T11-U9d2-classical-assembly`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,LocalExistenceProbe,LocalExistence,ConvolutionBound,GalileanClasses,PhysicalRecovery}.lean` (lanes 311/313/317/318: the two-space contract is inhabited, the forced mild solution `TorusForcedMildOn` exists and is unique, the physical field of an H³ datum is built with all its identities; read `research/T11/EXISTENCE_ROUTE.md` §"U9d status — lane 318" **including the analytical caution about the nonintegrable naive kernel**), `Section3/T10/{FourierCalculus,ForcePaths}.lean` (ForcePaths only if lane 312 has landed — check `ls`), `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean` (`reweightDatum` at real orders), the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/classical_assembly_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Sub-unit **U9d2** of U9d (`research/T11/EXISTENCE_ROUTE.md` §"U9d status — lane 318"): the second half of the U9d target. **Single allowed named input** (U9d1's conclusion, stated exactly as a
`def PersistenceInput : Prop`): for the data of the U9d statement, for every `m : ℕ` there is `u_m : ℝ → PeriodicSobolev m`, continuous on `Ico 0 T`, with the same coefficients as `u` on `Ico 0 T`
(if lane 319 has landed with a theorem of that shape, use it instead — check `ls Section3/T11/`). From it prove the U9d target verbatim (`EXISTENCE_ROUTE.md` / `REPORT_318.md`):
`∃ w : ClassicalSolutionT ν a g T, PeriodicLocalRegularity ν a g T w ∧ IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u`. Route: (i) **velocity** `w.velocity := torusPhysicalVelocity u` (lane 318;
already continuous, periodic, `initial`, datum path = `u`); its spatial smoothness at each time from the all-order coefficients (`FourierCalculus` decay/inversion + `PhysicalRecovery.torusPhysicalVelocity_component_contDiffOn`
generalized), time smoothness on `Ioo 0 T` from the Duhamel formula (the heat semigroup is differentiable in `t` on smooth data: `torusHeat_add` + the symbol; the Duhamel integral differentiates by the FTC
with the integrand continuous in `s`), divergence-free (the coefficients stay in the Leray range: `torusHeat_solenoidal`, the projected convection symbol and `P` are solenoidal); (ii) **pressure**: define
the coefficient pressure from the Leray complement of `(F(s) − Q(u,u))` (the `k ≠ 0` modes: `p̂(k) = −(k·ĝ(k))/(4π²|k|²)`-type formula with `ĝ` the unprojected convection + force; `k = 0` mode `0` ⇒ `PressureGaugeT`),
its physical field by the same inversion, smoothness, `pressure_gradient` (`∇p` datum = `F − Q − P(F − Q)`), `pressure_smooth`, `pressure_poisson` (`Δp = ∇·f − ∇·(∇·(u⊗u))` coefficientwise); (iii) **momentum**:
differentiate the Duhamel formula in `t` ⇒ `∂ₜû = −ν4π²|k|² û + P̂(F − Q)` ⇒ physical `∂ₜu − νΔu + (u·∇)u + ∇p = g` (`FourierCalculus` symbols for `Δ`, `∇`, and the convection identity
`(u·∇)u = ∇·(u⊗u)` under `divergence` — `Section4/A01/ConvectionDivergence` via `LocalTheory.convectionDivergenceT`); `projected`; (iv) assemble all `ClassicalSolutionT` fields (read the structure in
`Section3/T10/PeriodicData.lean`; `horizon_pos`, `initial`, `divergence`, `momentum`, `sobolev` (the continuous all-order datum paths), `pressure_gradient`, `pressure_smooth`, `pressure_gauge`, periodicity fields)
and `PeriodicLocalRegularity` (`sobolev_smooth`, `pressure_poisson`, `projected`). **Peeling rule**: at most ONE further named input if a step is out of reach (e.g. time-differentiability of the Duhamel
integral), stated exactly; everything else proved; record in `EXISTENCE_ROUTE.md` §"U9d2 status" (append only). (L+, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/ClassicalAssembly.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_classical_assembly.lean`.
2. Records `research/T11/ATTEMPTS_CLASSICAL_ASSEMBLY.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_320.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ClassicalAssembly` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[320-T11] ClassicalAssembly`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
