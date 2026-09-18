# Lane 326-T11-U9d2a-pressure — T11 U9d2a — the pressure of the mild solution: coefficient construction, physical field, and all pressure fields of `ClassicalSolutionT`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/326-T11-U9d2a-pressure` (git branch `erenup/326-T11-U9d2a-pressure`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/mild_pressure_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Sub-unit **U9d2a** of U9d2 (`EXISTENCE_ROUTE.md` §"U9d2 status — lane 320": pressure is the first missing block). **Single allowed named input**: `PersistenceInput T u` exactly as in lane 320's
`ClassicalAssembly.lean` (take it as hypothesis; lane 325 is discharging its source). Under the U9d hypotheses (`ν > 0`, `C`, `a ∈ initialClassT`, `g` smooth periodic, `T > 0`, `A`, `F`, `P`, `u` with
`TorusForcedMildOn C A P T u`) and `PersistenceInput T u`, **construct the pressure** and prove every pressure-related field of `ClassicalSolutionT` (read the structure in `Section3/T10/PeriodicData.lean`
for the exact field statements: `pressure_gradient`, `pressure_smooth`, `pressure_gauge`/`PressureGaugeT`, `pressure_periodic` (or whatever the periodicity field is called), and `PeriodicLocalRegularity.pressure_poisson`):
(i) coefficient pressure `p̂(t)(k)` for `k ≠ 0` from the Leray complement of `(F(t) − Q(u(t),u(t)))` — the scalar potential with `∇p̂ = (I − P)(F − Q)`, i.e. `p̂(k) = (k · (F̂ − Q̂)(k)) / (2πi|k|²)`-type
formula (derive it from `Section3/T10/Leray.lean`'s `periodicLeray` symbol; `k = 0` mode `0`); it is in every `H^m` by `PersistenceInput` + the convection bound (`ConvolutionBound.lean` at all orders via
`reweightDatum`) + the force paths (`ForcePaths.lean`); (ii) physical pressure `p(t,x) := ∑' k, p̂(t)(k) e^{2πik·x}` (scalar inversion as in `PhysicalRecovery.lean`/`FourierCalculus.lean`), periodic, smooth in `x`,
continuous (and, if you can, smooth) in `t` on `Ico 0 T`; (iii) `∇p` has datum `(I − P)(F − Q)` (`pressure_gradient` in the exact field shape), `pressure_gauge` (`k = 0` mode zero ⇒ `pressureMeanT = 0`),
`pressure_poisson` (`Δp = ∇·f − ∇·(∇·(u⊗u))` — coefficientwise `−4π²|k|² p̂ = 2πi k·(F̂ − Q̂)`, then the physical identity through the symbols of `FourierCalculus.lean` and `LocalTheory.scalarSpatialLaplacianT`/`convectionDivergenceT`).
Export `mildPressure`, `mildPressureCoeff`, and a bundled `MildPressureFields` record of the proved fields for the assembly lane. **Peeling rule**: at most ONE further named input (e.g. time
regularity of `t ↦ p̂(t)`), stated exactly; everything else proved; record in `EXISTENCE_ROUTE.md` §"U9d2a status" (append only). (L, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/MildPressure.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_mild_pressure.lean`.
2. Records `research/T11/ATTEMPTS_MILD_PRESSURE.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_326.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildPressure` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[326-T11] MildPressure`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
