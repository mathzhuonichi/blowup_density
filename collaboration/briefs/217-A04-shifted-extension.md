# Lane 217-A04-shifted-extension — close lane 215's single named input `ShiftedLocalExtension`: glue a restarted classical solution back into the original problem (lifespan ≥ b + L)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/217-A04-shifted-extension` (git branch `erenup/217-A04-shifted-extension`, based on lane 215's branch
`erenup/215-A04-restart-fixed-force` = `origin/erenup/integration` + `Section4/A04/RestartFixedForce.lean` (16 declarations: `shiftedSolution` — the restriction of a classical
solution from time `b` as a classical solution with datum `u(b,·)` and force `timeShift b f`; `restartFixedForce_of_memForceR`; `higherOrderBound_of_gronwall`; `restartBeyond_fixed`,
`extendsBeyond_fixed`, `lifespanInfiniteOfLocallyFinite_fixed` and their `…_of_memForceR` corollaries, all conditional on ONE named input `ShiftedLocalExtension`). Read that module
first, then `research/A04/REPORT_215.md` §3 and `research/A04/ATTEMPTS_RESTART_FIXED_FORCE.md`, A02's `Section4/A02/Restrict.lean` (§0: the local restatement of
`ClassicalSolutionR` — the exact `pressure_smooth`/`pressure_gradient`/`momentum`/`sobolev` fields), A02's `Maximal.lean`/`Patch*.lean` (`maximalLifespanR`, the `patch` of two solutions
with the same datum and force both starting at `0`; grep `theorem patch`), A02's uniqueness (`grep -rn "uniqueness\|unique" Section4/A02 Section4/A01/MildUniqueness.lean` — lane 188's
unconditional mild uniqueness on causal windows and its classical corollary), `Section4/A04/ForceShift.lean` (160: `timeShift`), lane 213's `A04/RestartWiring.lean`, `CLAUDE.md`,
`collaboration/HANDOFF.md` §0, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`A04.zeroSol`).
- **Satisfiability rule:** if one fact remains open, isolate it as ONE named hypothesis with the exact statement, satisfiable by nonzero solutions.

## Goal
`theorem shiftedLocalExtension : ShiftedLocalExtension` (the exact statement in `RestartFixedForce.lean`): for `w : ClassicalSolutionR ν a f T`, `b ∈ Ico 0 T`, and
`w₂ : ClassicalSolutionR ν (fun x => w.velocity (b,x)) (timeShift b f) L`, show `ENNReal.ofReal (b + L) ≤ maximalLifespanR ν a f`. Route (paper `appendix-a-local-theory.tex:147-157`,
the restart step): build the glued classical solution on `[0, b+L)`:
- **velocity**: `w.velocity` on `t < T`, `w₂.velocity (t - b, x)` on `t ≥ b`; on the overlap `[b, min T (b+L))` they agree by uniqueness: `shiftedSolution w b` (215) and `w₂` are classical
  solutions with the same datum and the same force from time `0`, so the classical uniqueness in the tree (A02's `patch`/lane 188 corollary — say which) gives equality of velocities
  on the common window. If `T ≤ b + L` is not given, split `T < b+L` (glue) vs `b + L ≤ T` (nothing to do: `w` itself witnesses).
- **pressure**: on the overlap the two pressures have the same gradient, so they differ by a function of `t` only; do NOT try to extend that function across `T`. Instead blend with a smooth
  time cutoff `θ : ℝ → ℝ`, `θ = 1` near `b`, `θ = 0` near `T` (Mathlib `ContDiffBump`/`smoothTransition`): pressure `:= w.pressure` on `t < b`, `θ t • w.pressure + (1 - θ t) • w₂.pressure(t-b)`
  on `[b, T)`, `w₂.pressure (t-b)` on `t ≥ T`. Its gradient equals the common gradient on the overlap (convex combination of equal gradients), and it is jointly smooth because near each
  seam only one summand is active.
- Discharge every field of the local `ClassicalSolutionR` restatement for the glued pair (`horizon_pos`, `initial`, `divergence`, `momentum`, `sobolev` — the Sobolev datum path is piecewise
  the two given paths, `pressure_gradient`, `pressure_smooth`, joint smoothness of the velocity on `Ico 0 (b+L) ×ˢ univ` — use the overlap identity to see the seam is fake), then
  `maximalLifespanR` is a sup/upper bound over horizons of classical solutions (check its definition and the lemma `le_maximalLifespanR_of_solution` or its equivalent in `Maximal.lean`).
Then the corollaries: `restartBeyond_of_memForceR'`, `extendsBeyond_of_memForceR'`, `lifespanInfiniteOfLocallyFinite_of_memForceR'` — lane 215's `…_of_memForceR` theorems with the
`extension` binder discharged (state them with no named input).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A04/ShiftedExtension.lean` (namespace `NSFormalization.Section4.A04`).
2. Records `research/A04/ATTEMPTS_SHIFTED_EXTENSION.md`, update `research/A04/COMPARISON.md` (which A04 statements are now unconditional for `MemForceR` forces), conformance
   `research/A04/axioms_shifted_extension.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.ShiftedExtension` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A04/REPORT_217.md`.
