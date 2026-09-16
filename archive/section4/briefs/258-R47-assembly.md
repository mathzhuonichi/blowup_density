# Lane 258-R47-assembly — Theorem 4.7 (thm:Rgrid) assembled: `RGridAPI.choose` of `research/R47/Spec.lean` from lane 233's record and the landed grid/flux lemmas (conditional only on I03's `CompactHomogeneousRealization` for the `L²_tḢ⁻¹_x` term)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/258-R47-assembly` (git branch `erenup/258-R47-assembly`, based on `origin/erenup/integration`). Read the target `research/R47/Spec.lean`
(`RGridFamily ν a g T δ reference n grids` — every field — and `RGridAPI.choose`; copy the statement token for token), `research/R47/RECONCILIATION.md` §4, `research/R47/COMPARISON.md`, then the
suppliers, all on integration: lane 233 `verification/Bindings/InsertionFromData.lean` (`insertionLifespanV2_of_data`: the R42 record from raw data; import caveat: not with `Bindings.Packet`),
lane 247 `Bindings/GridLemmas.lean` (`exists_ball_in_common_cell`), lanes 251/253 `Bindings/ForceCellIntegral.lean`, `Bindings/FluxCancellation.lean` (`velocity_gridObservation_eq`,
`force_gridObservation_eq'` on `[0,T)` for a record whose ball lies in a cell; hypothesis `hg : MemForceR A.g`), lane 249 `Bindings/MainThresholds.lean` (**template** for the rider: one record
per reference, uniqueness identification of the reference, history from `A.history`, force convergence from `forceConvergence`, the `E_T` limit squeezed from R42's registered rate),
lane 250 `Bindings/ScalingHomogeneous.lean` + `Section4/I03/HomogeneousScaling.lean` (`packetNegativeHomogeneous`/`correctionNegativeHomogeneous` bounds **conditional on `CompactHomogeneousRealization`**
— lane 255, running, closes it; you may take `CompactHomogeneousRealization` as the ONE named input of your final theorem), the R42 record fields (`Contracts/V1/InsertionFamily.lean:125-330`:
`velocityDifference_support`, `pressureDifference_support`, `forceDifference_ball`, `forceDifference_compact`, `history`, `energyRate`, `forceConvergence`; `Contracts/V2/InsertionLifespan.lean`:
`solution`, `lifespan`), `Bindings/InsertionLifespan.lean` (`memForceR_force`), `Contracts/V1/Data.lean` (§grid: `Grid`, `Grid.cell`, `gridObservation`; `mixedLebesgueENorm` `:251`; `energyENorm` §5),
the paper `04-whole-space.tex:297-330`, `CLAUDE.md`, `collaboration/HANDOFF.md` §0, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests; new files only. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`ν = T = 1`, `a = 0`, `g = 0`, `n = 0` and `n = 1`).
- **Statement fidelity:** `RGridAPI.choose` verbatim. **Peeling:** the ONLY permitted named input is `CompactHomogeneousRealization` (lane 250's exact `def`) for the `forceHomogeneousENorm 2 (-1)`
  summand of `force_convergence`; everything else must close from the tree. State the theorem as `rGrid_choose_of_realization (hreal : CompactHomogeneousRealization) : <choose's statement>`,
  and `rGridFamily_of_data` producing the record.

## Goal
Given `ν a g T δ reference n grids`: (1) `exists_ball_in_common_cell` gives `x₀, r`; (2) build the R42 record with the insertion ball pinned to `(x₀, r)` — check whether lane 233's constructor
exposes the ball (`A.scaling.correction.x₀`, `.r`) as parameters; if 233 fixes them internally, use the underlying I02 correction constructor with the given ball (see `Bindings/Correction.lean:142`
`correction (P) {T δ r}` — read what it takes) and re-run 233's chain, or isolate the ball choice as part of the construction (do NOT add a named input for it); (3) `force := A.force`,
`solution ε := (L.solution ε …)`, `force_mem` from `memForceR_force`, `history` from `A.history`, `forceDifference_compact` from the record, `velocity_/force_observations` from 251/253 with
`containingCell` from (1), `lifespan` from `L.lifespan`, `energy_convergence` as in 249, `force_convergence` = the sum of the three norms → 0: the inhomogeneous two from `forceConvergence` at
`(1,0)` (as `mixedLebesgueENorm 1 2` — prove the bridge `mixedLebesgueENorm 1 2 = forceSobolevENorm 1 0` on the compact difference or use whichever the Spec spells; **do not change the Spec**)
and `(2,−1)`, the homogeneous one from lane 250's bound on `g_ε − g = H_ε + F_ε` (correction + packet) under `hreal`; `velocity_support`, `pressure_support` (gauge `c t`), `force_support`
from the record's support fields (ball ⊆ cell).

## Deliverables
1. `verification/Bindings/GridAssembly.lean` (namespace `BlowupDensity.Bindings`), audit `research/R47/axioms_assembly.lean` (in `Contracts.V1.Data` vocabulary), records
   `research/R47/ATTEMPTS_ASSEMBLY.md`, update `research/R47/COMPARISON.md` (what is proved; the single remaining input and who closes it).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.GridAssembly` (silent), `lake env lean Bindings/GridAssembly.lean` (0 output), the audit, `make check`, `make test`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R47/REPORT_258.md`.
