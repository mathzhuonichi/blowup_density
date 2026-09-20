# Lane 334-T11-U9d2c-classical-assembly — T11 U9d2c: all-order time smoothness and the classical assembly (close the U9d target)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/334-T11-U9d2c-classical-assembly` (git branch `erenup/334-T11-U9d2c-classical-assembly`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,LocalExistenceProbe,LocalExistence,ConvolutionBound,ConvolutionBoundReal,FractionalSmoothing,Persistence,DuhamelHalfStep,PhysicalRecovery,ClassicalAssembly,MildPressure,MildMomentum,Restart,Maximal}.lean` — read the reports `research/T11/REPORT_{318,320,326,327,330}.md` and `research/T11/EXISTENCE_ROUTE.md` (all U9 status sections) first: `persistence_unconditional` (330: continuous realizations of the mild solution at every order, same horizon), `torusPhysicalVelocity` with datum path/initial/continuity (318), spatial smoothness + divergence-free (320, from `PersistenceInput`, which 330 now discharges: check how to instantiate it), the pressure with Poisson/gauge/gradient datum/spatial smoothness (326), first time derivative + momentum/projected equations (327). `Section3/T10/{PeriodicData,FourierCalculus,ForcePaths}.lean`, `Section3/T12/*.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/mild_classical_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Sub-unit **U9d2c** — close the U9d target (statement verbatim in `EXISTENCE_ROUTE.md` §U9d / `REPORT_318.md`; also `Persistence.lean`/`ClassicalAssembly.lean` restate its hypotheses):
`∀ ν > 0, ∀ C : TorusTwoSpaceContract ν, ∀ a g T, a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T → ∀ A F P u, IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F → (∀ t ≥ 0, IsPeriodicLerayDatum (F t) (P t)) → TorusForcedMildOn C A P T u → ∃ w : ClassicalSolutionT ν a g T, PeriodicLocalRegularity ν a g T w ∧ IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u`,
**with no named input** (`PersistenceInput T u` is now a theorem via 330's `persistence_unconditional` — instantiate it; if the shapes differ, prove the bridge). Two pieces:
(a) **all-order time smoothness** (the residual of 327): `velocity_smooth` and `pressure_smooth` of `ClassicalSolutionT` (read their exact statements in `Section3/T10/PeriodicData.lean`: joint `ContDiffOn ℝ ∞` on
`Ico 0 T ×ˢ univ` or as stated) for `torusPhysicalVelocity u` and `mildPressure g u`. Route: the mild equation holds at every order (the Duhamel formula is coefficientwise the same after reweighting —
`persistence_unconditional` + 330's coefficient identities), so 327's `mild_coeff_hasDerivAt` applies at every order; the time derivative `−ν4π²|k|²û + P̂(F − Q(u,u))` is again a continuous path at
every order (heat symbol bounded by one weight power; `Q` by the real-order bound `ConvolutionBoundReal.lean`; `F` by `ForcePaths.lean`) and is itself differentiable by the same argument (product rule for
the bilinear `Q` — its derivative is `Q(u',u) + Q(u,u')`), hence by induction the coefficient paths are `C^k` in time at every order for every `k`; then joint smoothness of the Fourier series from rapid
decay (`FourierCalculus.lean`) with the time derivatives of the coefficients (differentiate the series termwise: uniform convergence of the derivative series on compacts); continuity up to `t = 0` for
the function and one-sided derivatives at `0` if the field statement needs `Ico` (check; if the field is on `Ioo 0 T`, say so). Same for the pressure from 326's coefficient formula.
(b) **assembly**: build `w : ClassicalSolutionT ν a g T` field by field (`velocity`, `pressure`, `horizon_pos`, `velocity_smooth`, `pressure_smooth`, `initial` (318), `divergence` (320), `momentum` (327's
`momentum_of_mildPressure`), `sobolev` (the continuous all-order datum paths from 330/318), `pressure_gradient` (326), `velocity_periodic`/`pressure_periodic` (318/326), `pressure_gauge` (326)), then
`PeriodicLocalRegularity` (`sobolev_smooth`, `pressure_poisson` (326), `projected` (327)) and `IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u` (318's `torusPhysicalVelocity_datum`). State the final
theorem exactly as the U9d target (`theorem mild_to_classical …`) and add the corollary in the shape lane 321's `restart` needs (check `Restart.lean`: the existence of a `ClassicalSolutionT` with
`PeriodicLocalRegularity` from an H³ datum and a smooth force on the Picard horizon — combine with 313/317's `torusForcedPicard_exists` and 330's `exists_continuous_lerayForcePath`), named
`exists_classical_of_picard`. **Peeling rule**: if (a)'s induction is out of reach in one run, deliver (b) with (a) as the single named input stated exactly (`def MildTimeSmoothInput : Prop := …`
mentioning only the two `ContDiffOn` facts), and say so; a stub is discarded. (L+, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/MildClassical.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_mild_classical.lean`.
2. Records `research/T11/ATTEMPTS_MILD_CLASSICAL.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_334.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildClassical` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[334-T11] MildClassical`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
