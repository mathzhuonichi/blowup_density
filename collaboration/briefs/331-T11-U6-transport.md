# Lane 331-T11-U6-transport — T11 U6 — solution transport under smooth change of variables (`transformed_solution`, `to_unit`, `from_unit`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/331-T11-U6-transport` (git branch `erenup/331-T11-U6-transport`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,GalileanClasses,Rescaling,Uniqueness,MeanIdentity,Restart,Maximal,Persistence,ClassicalAssembly,DuhamelHalfStep}.lean` (all T11 units landed so far: U1–U5, U7, U10, U11, U15; `GalileanClasses.lean` has the translation isometry and class transports, `Rescaling.lean` the viscosity algebra, `MeanIdentity.lean` translation/mean lemmas, `Restart.lean` the `restart` theorem from the existence input), `Section3/T10/{FourierCalculus,ForcePaths}.lean`, `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/transport_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U6** of `T11_SPLIT.md` §1: one shared constructor — given `w : ClassicalSolutionT ν a f T`, a `C^∞` time-dependent translation `X : ℝ → Space` and constants `(α, β, γ)`, rebuild a
`ClassicalSolutionT` for the transformed data, transporting all fields (read the structure in `Section3/T10/PeriodicData.lean`: chain rules for the time derivative / spatial Laplacian /
pressure gradient / divergence under `(t,x) ↦ (αt, βx + X(t))`-type maps; the datum path via `GalileanClasses.translation_preserves_sobolev` (translation isometry) and the reweighting/scaling
of coefficients; the gauge via translation invariance of `meanT` (`MeanIdentity.meanT_translate`); periodicity; the force/initial classes via `GalileanClasses`/`Rescaling`) — then the three
fields verbatim from `research/T11/probes/api_on_canonical.lean`: `transformed_solution` (of `PeriodicMeanReductionAPI`: the Galilean-transformed fields `galileanVelocityT`/`galileanPressureT`/
`galileanForceT` of `Section3/T11/LocalTheory.lean` form a `ClassicalSolutionT` for the centred datum with `PeriodicLocalRegularity`), `to_unit` and `from_unit` (of `PeriodicViscosityRescalingAPI`:
the unit-viscosity rescaling maps and their inverses transport solutions with regularity). Build the general constructor once and instantiate it three times; prove every field, no named input
expected (if the `PeriodicLocalRegularity` transport needs the `pressure_poisson`/`projected` chain rule, prove it — it is the same computation). (L, sol.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/Transport.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_transport.lean`.
2. Records `research/T11/ATTEMPTS_TRANSPORT.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_331.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Transport` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[331-T11] Transport`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
