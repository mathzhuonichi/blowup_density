# Lane 253-R47-flux-cancellation — close lane 251's single named input `hcompactMomentumIntegral`: the spatial flux terms of the momentum-equation difference integrate to zero over a cell containing the insertion ball

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/253-R47-flux-cancellation` (git branch `erenup/253-R47-flux-cancellation`, based on lane 251's branch `erenup/251-R47-force-cell-integral` =
`origin/erenup/integration` + `verification/Bindings/ForceCellIntegral.lean` (14 theorems; read it fully — especially the exact statement of the named input `hcompactMomentumIntegral` and the
theorems `insertion_momentum_difference`, `velocityDifference_cell_integral_zero`, the time-derivative integral lemma, and `force_gridObservation_eq`) + `research/R47/REPORT_251.md`,
`research/R47/ATTEMPTS_FORCE_CELL.md` (the precise Lean type, the R42 fields available, the satisfiability argument, failed routes)). Also read `verification/Bindings/GridLemmas.lean`
(lane 247), the registered residual/momentum vocabulary (`grep -rn "Residual\|residual" verification/Contracts/V1/Data.lean verification/Contracts/V1/Packet.lean` — how `Residualν(u,p)` is
spelled: `∂_t u + (u·∇)u + ∇p − νΔu`), the R42 record fields `velocityDifference_support`, `velocityDifference_divFree`, `pressureDifference_support`, `velocity_smooth`, `pressure_smooth`
(`Contracts/V1/InsertionFamily.lean:125-330`), `Section4/R42/Assembly.lean` (`inserted_equation_slab`), and the compact-support derivative lemmas in the tree
(`grep -rn "integral.*deriv\|integral_fderiv\|integral_div\|HasCompactSupport.*integral" formalization/NSFormalization/Paper3 formalization/NSFormalization/Source | head`, e.g.
`Paper3.setIntegral_component_eq_zero`, `Paper3.integral_timeDerivative_component_eq_zero`, and Mathlib's `integral_fderiv_eq_zero_of_hasCompactSupport`/`Mathlib.Analysis.Calculus.Deriv.Support`),
the paper `04-whole-space.tex:305-320` (eq:gridforce and the sentence "the boundary terms vanish because all differences are supported strictly inside the cell"), `CLAUDE.md`,
`collaboration/HANDOFF.md` §0, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests (251's file is on your base but unmerged — do not edit
  it either); new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s.
- **Satisfiability rule:** if one step genuinely resists, isolate it as ONE named hypothesis with the exact statement, satisfiable by the actual inserted family.

## Goal (in `verification/Bindings/FluxCancellation.lean`, namespace `BlowupDensity.Bindings`)
1. `compactMomentumIntegral : <the exact statement of hcompactMomentumIntegral>` for every R42 record `A`, scale `ε ∈ Ioc 0 A.ε₀`, cell `C ⊇ ball x₀ r`, `t ∈ Ioo 0 T`. Route: expand
   `Residualν(u_ε,p_ε) − Residualν(v,π)`; the difference `w = u_ε − v` (and `δp = p_ε − π` up to a spatial constant) is smooth and supported in the ball at each time; write
   `(u_ε·∇)u_ε − (v·∇)v = div(u_ε ⊗ u_ε − v ⊗ v)` (both fields divergence-free; the tensor difference `u_ε⊗u_ε − v⊗v = w⊗u_ε + v⊗w` is supported in the ball), `∇δp`, `−νΔw = −ν div ∇w` —
   each a spatial derivative of a smooth field compactly supported inside the open cell interior, so its integral over `C` (= over `ℝ³`) vanishes (Mathlib: `integral_fderiv_eq_zero_of_hasCompactSupport`
   or the tree's `Paper3` lemma), leaving `∫_C ∂_t w = ∫_{ℝ³} ∂_t w`. Handle the spatial constant gauge in `pressureDifference_support` (`∇(δp − c t) = ∇δp`).
2. `forceDifference_cell_integral_zero'`, `force_gridObservation_eq'`: lane 251's conditional theorems with the input discharged (unconditional for the R42 record with `hg : MemForceR A.g`).
3. Audit `research/R47/axioms_flux_cancellation.lean`; records `research/R47/ATTEMPTS_FLUX.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.FluxCancellation` (silent), `lake env lean Bindings/FluxCancellation.lean` (0 output), the audit, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R47/REPORT_253.md`.
