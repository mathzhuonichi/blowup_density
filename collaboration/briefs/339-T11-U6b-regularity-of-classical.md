# Lane 339-T11-U6b-regularity-of-classical — T11 U6b: every classical periodic solution has `PeriodicLocalRegularity` (smooth datum paths, Poisson, projected)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/339-T11-U6b-regularity-of-classical` (git branch `erenup/339-T11-U6b-regularity-of-classical`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,EnergyIdentity,Transport,ClassicalAssembly,MildPressure,MildMomentum,CriterionBridge}.lean` (lane 335's `EnergyIdentity.lean`: `hasDerivAt_velocityCoeffT` — differentiation of the Fourier-coefficient integral under the integral sign from `velocity_smooth` alone, via `Paper1.periodicFourierCoeff_eq_cube` + `hasDerivAt_cubeIntegral_of_contDiffOn`; `velocityDerivCoeffT_momentum`; lane 331's `Transport.lean`: `pressure_poisson_galilean`, `spatialDivergence_directional_eq_zero`; lane 320's `ClassicalAssembly.classicalSolutionT_projected`; read `research/T11/REPORT_331.md` §3 and `REPORT_335.md` first), `Section3/T10/{PeriodicData,FourierCalculus,ForcePaths}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/classical_regularity_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U6b** (the residual of lanes 331 and 321): **every classical periodic solution has the manuscript regularity** —
`theorem periodicLocalRegularity_of_classical : ∀ ν > 0, ∀ a ∈ initialClassT, ∀ f ∈ forceClassT, ∀ T (w : ClassicalSolutionT ν a f T), PeriodicLocalRegularity ν a f T w`
(read both structures in `Section3/T10/PeriodicData.lean` and `Section3/T11/LocalTheory.lean`). The three clauses: (1) `sobolev_smooth` — for every `m : ℕ` a datum path
`G : ℝ → PeriodicSobolev m` with `IsPeriodicSobolevPathOn m (Ico 0 T) w.velocity G ∧ ContDiffOn ℝ ∞ G (Ico 0 T)` (or exactly as stated): build `G t` as the datum of the smooth slice
(`CriterionBridge.exists_periodicDatum_smooth` / `ForcePaths.continuous_datum_path`), then prove `ContDiffOn ℝ ∞` of the `lp`-valued path by iterating lane 335's differentiation under the
integral (`hasDerivAt_velocityCoeffT` gives the first derivative of each coefficient; the `k`-th time derivative of each coefficient is the coefficient of `∂ₜ^k u`, again a smooth periodic slice;
summability with the weight `W(k)^m` from rapid decay (`FourierCalculus.lean`) uniformly on compacts of `Ico 0 T`; the `lp`-valued derivative via termwise differentiation with a uniform dominating
bound — Tannery-type argument as in lane 331's translation-family continuity; induct on the derivative order with `contDiffOn_succ_iff_hasFDerivWithinAt`-style lemmas); (2) `pressure_poisson`
from `momentum` + `divergence` (take the divergence of the momentum equation; `∂ₜ` and `Δ` commute with `div`, `div u = 0`; lane 331's `spatialDivergence_directional_eq_zero`/`pressure_poisson_galilean`
show the computation; `Section4/A01/ConvectionDivergence` for `div((u·∇)u) = ∇·(∇·(u⊗u))` under `div u = 0`); (3) `projected` = `ClassicalAssembly.classicalSolutionT_projected`. Then the
corollaries lane 331 left conditional: `transformed_solution`, `to_unit`, `from_unit` fields unconditionally (compose with 331's `transformed_solution_fields`, `to_unit_of_regularity`,
`from_unit_of_regularity`), and `regularity_of_solution` in the shape lane 321's `PeriodicLocalTheoryAPI.regularity` needs. **No named input**; honest partial with the exact obstacle if stuck. (L, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_classical_regularity.lean`.
2. Records `research/T11/ATTEMPTS_CLASSICAL_REGULARITY.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_339.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ClassicalRegularity` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[339-T11] ClassicalRegularity`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
