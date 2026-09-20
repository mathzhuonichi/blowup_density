# Lane 251-R47-force-cell-integral — eq:gridforce: the inserted force difference `g_ε − g` has zero integral over the cell containing the insertion ball (the missing hypothesis of lane 247's `gridObservation_locality` for the force observations)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/251-R47-force-cell-integral` (git branch `erenup/251-R47-force-cell-integral`, based on lane 247's branch `erenup/247-R47-grid-lemmas` =
`origin/erenup/integration` + `verification/Bindings/GridLemmas.lean` (`exists_ball_in_common_cell`, `gridObservation_locality` — read its exact hypotheses: support in `B ⊆ cell k₀`,
integrability on the cell, **zero vector integral of the difference on the cell**)). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0, the top 40 lines of `logs/LESSONS.md`,
`research/R47/REPORT_247.md` §3 (the velocity difference's zero integral follows from `velocityDifference_divFree` via `Paper3.setIntegral_component_eq_zero`; the **force** difference needs the
paper's argument), `research/R47/RECONCILIATION.md`, `research/R47/Spec.lean` (`RGridFamily.force_observations`), the paper `04-whole-space.tex:297-330` (Theorem 4.7's proof — find the display
`eq:gridforce` and the sentences around it: the force difference `g_ε − g = H_ε + F_ε` satisfies the momentum equation of the difference `∂_t(u_ε − v) + … = g_ε − g` with the nonlinear/pressure
terms; integrating over the containing cell, the time derivative of the zero-mean velocity difference vanishes, the divergence-form terms integrate to boundary terms that vanish because the
difference is supported strictly inside the cell, and the pressure gradient integrates to zero for the same reason — read exactly what the paper claims), the registered R42 record
`verification/Contracts/V1/InsertionFamily.lean:125-330` (`velocityDifference_support`, `velocityDifference_divFree`, `pressureDifference_support`, `forceDifference_ball`,
`forceDifference_compact`, `momentum`, `incompressible`, `velocity_formula`/`force_formula`, `history`) and `Section4/R42/Assembly.lean` (`inserted_equation_slab`: the momentum identity of the
inserted velocity on the slab; `inserted_divergence_slab`), `Paper3` lemmas on cell integrals (`Paper3.setIntegral_component_eq_zero`, divergence-theorem-free arguments: a compactly supported
smooth field's divergence integrates to zero — grep `integral_div`, `divergence`, `setIntegral` in `Paper3/`, `Source/`), and `Contracts/V1/Data.lean` §grid (`Grid.cell`, `cellAverage`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests; new files only. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s.
- **Satisfiability rule:** if one analytic fact remains open (e.g. a divergence-theorem step), isolate it as ONE named hypothesis with the exact statement, satisfiable by the actual inserted family.

## Goal (in `verification/Bindings/ForceCellIntegral.lean`, namespace `BlowupDensity.Bindings`)
1. `velocityDifference_cell_integral_zero`: for an `InsertionFamilyAPI` record `A`, `ε ∈ Ioc 0 A.ε₀`, `t ∈ Ico 0 T`, and a cell `cell k₀ ⊇ ball x₀ r` (the family's ball), `∫ x in cell k₀, (A.velocity ε (t,x) − v(t,x)) = 0`
   (each component) — from `velocityDifference_divFree` + support + `Paper3.setIntegral_component_eq_zero` (as 247's report says).
2. `forceDifference_cell_integral_zero`: same for `A.force ε (t,·) − g(t,·)` for `t ∈ Ioo 0 T` (or the paper's time range) — the eq:gridforce argument: write `g_ε − g` from the two momentum
   equations as `∂_t w + (divergence-form nonlinear terms) + ∇(p_ε − π) − νΔw` with `w := u_ε − v` supported in the ball; integrate over the cell: `∫ ∂_t w = d/dt ∫ w = 0` by item 1 (differentiate
   under the integral — `w` smooth, compactly supported in the cell), `∫ ∇(·) = 0` and `∫ Δw = 0`, `∫ div(·) = 0` for fields supported strictly inside the cell (compact support ⇒ integral of a
   derivative vanishes). State precisely which R42 fields you use; if the momentum identity of the difference is not directly available in the record, derive it from `A.momentum` and the
   reference's `ClassicalSolutionR` momentum (`A.reference`).
3. Corollary: with lane 247's `gridObservation_locality`, `gridObservation grid (A.force ε (t,·)) = gridObservation grid (g(t,·))` and the velocity analogue, for every grid whose cell contains
   the ball — the `force_observations`/`velocity_observations` fields of `research/R47/Spec.lean` for the R42 record (time range as the spec states; say what holds at `t = 0`).
4. Audit `research/R47/axioms_force_cell_integral.lean`; records `research/R47/ATTEMPTS_FORCE_CELL.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.ForceCellIntegral` (silent), `lake env lean Bindings/ForceCellIntegral.lean` (0 output), the audit, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R47/REPORT_251.md`.
