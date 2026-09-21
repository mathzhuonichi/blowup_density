# Lane 259-R46-closure — Proposition 4.6, second and third clauses: `completedHomogeneousDensity` and `strongTrajectoryClosure` of `research/R46/Spec.lean` (conditional only on I03's `CompactHomogeneousRealization`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/259-R46-closure` (git branch `erenup/259-R46-closure`, based on `origin/erenup/integration`). Read the target `research/R46/Spec.lean`
(fields `completedHomogeneousDensity : ∀ a ∈ initialClassR, ∀ ν > 0, ∀ T > 0, CompletedDenseHomogeneous 2 (-1) (breakdownSetIn forceClassCompact ν a T)` and `strongTrajectoryClosure` (raw-data
form: `∀ a ν T g, MemForceR g → ∀ δ > 0, ∀ R : ClassicalSolutionR ν a g (T+δ), ∃ P A, A.a = a ∧ A.scaling.correction.T = T ∧ … ∧ (∀ ε ∈ Ioc 0 A.ε₀, MemForceR (A.force ε) ∧ maximalLifespanR ν a (A.force ε) = ofReal T ∧ ∃ U, …) ∧ Tendsto (energyENorm …) ∧ Tendsto (three-norm sum …)`)
— copy both token for token), `research/R46/RECONCILIATION.md` (§3 proof dependencies; the addendum on `mixedLebesgueENorm`), `research/R46/COMPARISON.md`, then the suppliers on integration:
lane 233 `verification/Bindings/InsertionFromData.lean` (`insertionLifespanV2_of_data`; import caveat: not with `Bindings.Packet`), lane 249 `Bindings/MainThresholds.lean` (**template**: energy
limit from `energyRate`, force convergence from `forceConvergence`, uniqueness identification), lane 250 `Bindings/ScalingHomogeneous.lean` + `Section4/I03/HomogeneousScaling.lean` (the homogeneous
bounds `‖F_ε‖_{L²Ḣ⁻¹} ≤ Cε^β`, `‖H_ε‖ ≤ Cε^{β+1}` conditional on `CompactHomogeneousRealization` — lane 255 closes it; you may take it as the ONE named input), `Contracts/V2/HomogeneousPartial.lean`
(`approxCompactHomogeneous : ∀ q ≥ 1, q ≠ ⊤, ∀ s, …` — the homogeneous completed approximation by smooth compact forces; read its exact statement and binding), lane 252
`Bindings/CompactClassDensity.lean` (`density_compact`), lane 256's branch `erenup/256-R46-sobolev-density` (running; `git show` its `Bindings/CompletedSobolevDensity.lean` for the Sobolev-clause
route: B01 approx + relative density + path additivity + triangle inequality — copy it with the homogeneous vocabulary `IsHomogeneousPath (-1)`, `forceHomogeneousENorm`), `Contracts/V1/Data.lean`
(`CompletedDenseVia`/`CompletedDenseHomogeneous` `:732-750`, `IsHomogeneousPath` `:375`, `forceHomogeneousENorm` `:390`, `energyENorm` §5, `mixedLebesgueENorm` `:251`), the paper
`04-whole-space.tex:218-296` (esp. `:264-275`: the homogeneous density uses the **scaling** of the inserted compact difference, not an embedding), `CLAUDE.md`, `collaboration/HANDOFF.md` §0,
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests; new files only. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s (`ν = T = 1`, `a = 0`, `g = 0`, target `b = 0`).
- **Statement fidelity:** the two Spec fields verbatim. **Peeling:** the ONLY permitted named input is `CompactHomogeneousRealization` (lane 250's `def`); state
  `strongTrajectoryClosure_of_realization (hreal : …)` and `completedHomogeneousDensity_of_realization (hreal : …)`; everything else from the tree. If the homogeneous density needs a
  homogeneous relative-density step for `F_c` that is not derivable from the scaling bounds (e.g. the target's approximant `g` must itself be compact — `approxCompactHomogeneous` gives that),
  say exactly where.

## Goal (in `verification/Bindings/CompletedClosure.lean`, namespace `BlowupDensity.Bindings`)
1. `strongTrajectoryClosure_of_realization`: from raw data, lane 233's record `L`; pin the correction fields as the Spec requires; `MemForceR (A.force ε)` (`memForceR_force`), lifespan and solution
   from `L`; `Tendsto (energyENorm T (A.velocity ε − R.velocity))` from `energyRate` (249's squeeze); the three-norm sum: `forceSobolevENorm 1 0`/`mixedLebesgueENorm 1 2` and `forceSobolevENorm 2 (-1)`
   from `forceConvergence` (subcritical: `0 < 2/1 − 3/2`, `−1 < 2/2 − 3/2`), `forceHomogeneousENorm 2 (-1)` from lane 250's bounds on `H_ε + F_ε` (sum ≤ sum of bounds; `ε^β → 0`).
2. `completedHomogeneousDensity_of_realization`: given a homogeneous target `b` (`MemBochnerDatum 2 (-1)`) and `r`: `approxCompactHomogeneous` gives a smooth compact `g` with a homogeneous
   path within `r/2`; if `T_max(a,g) ≤ T`, take `f = g`; else item 1's family gives `f = A.force ε ∈ F_c` (compact closure, lane 252) with `T_max = T` and `‖f − g‖_{L²Ḣ⁻¹} < r/2`; combine paths
   (homogeneous path additivity — grep `isHomogeneousPath_add` in `Contracts/V1/DatumLemmas.lean`/`Section4/D01`; if absent, prove it) and the triangle inequality.
3. Audit `research/R46/axioms_closure.lean`; records `research/R46/ATTEMPTS_CLOSURE.md`; update `research/R46/COMPARISON.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.CompletedClosure` (silent), `lake env lean Bindings/CompletedClosure.lean` (0 output), the audit, `make check`, `make test`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R46/REPORT_259.md`.
