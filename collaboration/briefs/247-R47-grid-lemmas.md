# Lane 247-R47-grid-lemmas — the two geometric lemmas Theorem 4.7 (thm:Rgrid) needs: a ball inside a common cell of finitely many grids, and locality of grid observations

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/247-R47-grid-lemmas` (git branch `erenup/247-R47-grid-lemmas`, based on `origin/erenup/integration`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0,
the top 40 lines of `logs/LESSONS.md`, the registered grid vocabulary `verification/Contracts/V1/Data.lean` (`structure Grid`, `Grid.cell`, `gridObservation grid z : (Fin 3 → ℤ) → Space` — read
the definitions and docstrings around `:770-800`, and the paper lines they cite: `04-whole-space.tex:286-296` "a complete uniform Cartesian grid of ℝ³ with cell size h … cell averages"),
`research/R47/RECONCILIATION.md` §4 (proof dependencies), the reconciled statement `git show erenup/246-SPEC-r47-spec:research/R47/Spec.lean` (fields `containingCell`, `velocity_observations`,
`velocity_support`), and the paper `04-whole-space.tex:297-320` (the proof of Theorem 4.7: "choose the insertion ball inside a cell of every grid; fields supported in the ball have the same
cell averages as the reference on every other cell, and on the containing cell the average of a divergence-free compactly supported difference vanishes / the difference integrates to zero" —
read exactly what the paper claims and why).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules; new files only. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s.
- **Statement fidelity:** state the lemmas in the registered `Data.Grid`/`gridObservation` vocabulary; since `formalization/` cannot import `Contracts`, put the module in
  `verification/Bindings/GridLemmas.lean` (Bindings may import Contracts) unless a local restatement of `Grid`/`gridObservation` already exists in `Section4/` (grep first).

## Goal
1. `exists_ball_in_common_cell : ∀ (n : ℕ) (grids : Fin n → Grid) (x : Space), ∃ x₀ r, 0 < r ∧ ∀ i, ∃ k, Metric.ball x₀ r ⊆ (grids i).cell k` (and, if the paper needs it near a prescribed point,
   the version with `x₀` in a given open set / ball). Route: cells are open cubes (or half-open — read the definition); the finitely many cell boundaries are a closed null set, pick `x₀` off all of
   them and `r` = min distance to the boundaries.
2. `gridObservation_locality`: if `z₁ − z₂` is supported in a set `B` with `B ⊆ (grid).cell k₀` and (per the paper) the difference has zero cell integral on `k₀` (state exactly what the
   paper uses: divergence-free + compact support in the cell ⇒ the average over the cell vanishes? or the observation is a cell average and the difference integrates to zero?), then
   `gridObservation grid z₁ = gridObservation grid z₂`. Read `gridObservation`'s definition first and prove the strongest true locality statement; if the paper's argument needs an extra
   hypothesis (e.g. zero mean on the containing cell), state it as an explicit hypothesis (this is not a "named input" — it is a genuine hypothesis of the lemma) and note how the inserted
   family satisfies it (`velocityDifference_divFree`, the packet's mean-zero property — grep `mean`/`zero_mean` in `Contracts/V1/Packet.lean`).
3. Audit `research/R47/axioms_grid_lemmas.lean`; records `research/R47/ATTEMPTS_GRID_LEMMAS.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.GridLemmas` (or the formalization module), `lake env lean` on the file (0 output), the audit, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R47/REPORT_247.md`.
