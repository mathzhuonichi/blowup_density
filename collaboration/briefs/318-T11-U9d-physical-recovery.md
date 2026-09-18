# Lane 318-T11-U9d-physical-recovery — T11 U9d: physical recovery — from the forced mild coefficient solution to a `ClassicalSolutionT` with `PeriodicLocalRegularity` on the common horizon

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/318-T11-U9d-physical-recovery` (git branch `erenup/318-T11-U9d-physical-recovery`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,LocalExistenceProbe,LocalExistence,ConvolutionBound,GalileanClasses}.lean` (lanes 311/313/317: the two-space contract now has an inhabitant `torusTwoSpaceContract_nonempty'`, the forced mild solution `TorusForcedMildOn` exists and is unique), `Section3/T10/FourierCalculus.lean` (inversion, decay), `Section3/T12/*.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/physical_recovery_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U9d** (`research/T11/EXISTENCE_ROUTE.md` §"U9b status", item U9d — read it and lane 317's `REPORT_317.md`): **physical recovery on a common horizon** — prove, verbatim as stated there,
```lean
∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν) (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
  a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
  ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
    IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F → (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) → TorusForcedMildOn C A P T u →
    ∃ w : ClassicalSolutionT ν a g T, PeriodicLocalRegularity ν a g T w ∧ IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u
```
Route (R2, `EXISTENCE_ROUTE.md`): (i) **all-order bootstrap on the common horizon**: the mild coefficient solution `u` of order 3 is in fact smooth in `x` at every time — from the Duhamel formula with
the heat smoothing (`torusHeatSmoothing_norm_le`, `torusSmoothingKernel_integrable`) and the convolution bound (`ConvolutionBound.lean`) iterate one order at a time (`H^m → H^{m+1}` on `(0,T)`,
uniform on compacts of `(0,T]`, plus the datum's own regularity at `t = 0` since `a ∈ initialClassT` is smooth); (ii) **physical velocity**: define `w.velocity (t,x) := ∑' k, û(t)(k) e^{2πik·x}`
(componentwise; `FourierCalculus.periodic_component_eq_tsum`-style inversion for summable coefficients; smoothness in `x` from rapid decay; smoothness/continuity in `t` from the Duhamel
formula), prove periodicity, divergence-free (`torusHeat_solenoidal`, Leray range), `initial` (`t = 0` gives `a` via `IsPeriodicDatum 3 a A` + inversion + `T01.torus_data.datum_unique`); (iii)
**pressure**: `w.pressure` from the Leray complement of the convection + force (coefficientwise; the `k = 0` mode zero → `PressureGaugeT`), smoothness, `pressure_gradient`, and the momentum
equation `w.momentum` from the mild equation by differentiating the Duhamel formula in `t` (time derivative of the heat semigroup on smooth data: `torusHeat_add`/coherence + the symbol identity);
(iv) `PeriodicLocalRegularity` (three fields: `sobolev_smooth` from (i), `pressure_poisson`, `projected`) and `IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u` (the datum of the constructed
velocity at time `t` is `u t` — by construction + uniqueness of data). **Peeling rule**: this is long; if one sub-step is out of reach in this lane, name exactly ONE input with its exact statement
(e.g. the `H^m → H^{m+1}` bootstrap step, or the time-differentiability of the Duhamel integral), prove everything else, and write the residual precisely in `EXISTENCE_ROUTE.md` §"U9d status" (append
only). If the whole target is too large for one run, deliver (ii)+(iii) fully (physical fields from a coefficient path with all-order regularity assumed as the single named input) — say so. (L+, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/PhysicalRecovery.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_physical_recovery.lean`.
2. Records `research/T11/ATTEMPTS_PHYSICAL_RECOVERY.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_318.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.PhysicalRecovery` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[318-T11] PhysicalRecovery`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
