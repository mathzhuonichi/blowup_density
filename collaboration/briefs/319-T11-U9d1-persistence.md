# Lane 319-T11-U9d1-persistence — T11 U9d1 — persistence of regularity: the H³ forced mild solution stays in every H^m on the common horizon

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/319-T11-U9d1-persistence` (git branch `erenup/319-T11-U9d1-persistence`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/persistence_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Sub-unit **U9d1** of U9d (`research/T11/EXISTENCE_ROUTE.md` §"U9d status — lane 318": the general all-order bootstrap is the first unproved obligation). Target (state it exactly in the module
and prove it; it is the first half of the U9d statement):
for `ν > 0`, `C : TorusTwoSpaceContract ν`, `T > 0`, `a ∈ initialClassT` (smooth ⇒ it has a datum at every order, `CriterionBridge.exists_periodicDatum_smooth`), `g` smooth periodic (so by lane 312 —
or, if 312 has not landed, by `CriterionBridge`/`FourierCalculus` slicewise — `g` has a coefficient path at every order), `A : PeriodicSobolev 3` its datum, `F`/`P` the order-3 force/projected-force
paths, and `u` with `TorusForcedMildOn C A P T u`: **for every `m : ℕ` there is `u_m : ℝ → PeriodicSobolev m` with the same coefficients as `u` on `Ico 0 T`** (`∀ t ∈ Ico 0 T, ∀ i k, (u_m t).1 i k = (u t).1 i k`),
`ContinuousOn u_m (Ico 0 T)` (or `Icc`), and bounded on compact subintervals. Route — **half-order steps, not whole-order** (the whole-order step has the nonintegrable kernel `(t−s)^{-1}`): the Duhamel
formula `u(t) = e^{νtΔ}A + ∫₀ᵗ e^{ν(t−s)Δ} (P(s) − Q(u(s),u(s))) ds` with the convection `Q : H^{r} × H^{r} → H^{r−1}` (generalize lane 317's bound to real orders `r ≥ 3` via `reweightDatum`: the same Peetre/Cauchy–Schwarz
argument, or the product estimate `H^{r} · H^{r} ⊂ H^{r}` for `r > 3/2` combined with the derivative symbol) and the smoothing `‖e^{νtΔ}‖_{H^{s} → H^{s+σ}} ≤ C (νt)^{-σ/2}` (lane 311's `torusHeatSmoothing_norm_le`, generalized to
fractional `σ` if only `σ = 1` is there — say which): gain `σ = 3/2` from `H^{r−1}` to `H^{r+1/2}` with the integrable kernel `(t−s)^{-3/4}`; iterate `r = 3, 3.5, 4, …` on `(0,T)`; regularity at `t = 0` from the
smooth datum via the same formula (the free term is in every `H^m` since `a` is smooth; the Duhamel term gains). Alternatively prove **persistence** directly: the order-`m` Picard solution exists on a horizon
`T_m` (lane 313's `torusForcedPicard_exists` at order `m` if the contract generalizes; else the bootstrap) and agrees with `u` by uniqueness (`torusForcedMildOn_unique`), then extend `T_m` to `T` by a Grönwall
bound of `‖u_m‖` in terms of `sup ‖u‖_{H³}` — choose the route you can finish. **Peeling rule**: if one analytic step is out of reach, name exactly ONE input with its exact statement (e.g. the real-order
convolution bound or the fractional smoothing estimate), prove everything else from it, and record it in `EXISTENCE_ROUTE.md` §"U9d1 status" (append only). (L, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/Persistence.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_persistence.lean`.
2. Records `research/T11/ATTEMPTS_PERSISTENCE.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_319.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Persistence` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[319-T11] Persistence`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
