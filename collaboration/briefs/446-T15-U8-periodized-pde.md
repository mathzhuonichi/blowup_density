# Lane 446-T15-U8-periodized-pde — T15 U8: the periodized fields satisfy the Navier–Stokes momentum equation, are divergence-free and start from zero (transport core)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/446-T15-U8-periodized-pde` (git branch `erenup/446-T15-U8-periodized-pde`, based on `origin/erenup/integration-section3`:
`Section3/T15/{Bridges,ParsevalZero,HaarBridge,Scaling,Placement,SingleCopy}.lean` — lane 384's raw-field `PlacementData`/`ScalingAPI` (`Scaling.lean:106`; the `solution` field `:301-305` asks for a
`ClassicalSolutionT ν 0 (periodizedScaledForce …) place.T` with velocity `periodizedScaledVelocity` and pressure `normalizedScaledPressure`; the raw packet clauses at `:485-491`: `zeroPastField u/p` smooth on
`Iio 1 ×ˢ univ`, the residual identity `navierStokesResidual ν (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t,x)`, `spatialDivergence (zeroPastField u) = 0`), lane 421's single copy
(`velocity/pressure/force_singleCopy`, summability, the four lattice lemmas), lane 376's placement (slice supports inside the cube), lane 362's `Bridges.lean` (vendor `periodize` lemmas:
`periodize_locally_eq_sum`, `periodize_add_lattice`, `contDiff_periodize`, `contDiffOn_periodize`), the Section 4 scaling PDE facts (`grep -rn "scaled_equation\|scaled_divergence_free\|source_time_lt_one\|navierStokesResidual_eq" formalization/NSFormalization/Section4 formalization/NSFormalization/Source` — the canonical theorems that `verification/Bindings/Scaling.lean:58,79,88,100` wrap; `formalization/` cannot import `Bindings`),
and the T11 canonical `ClassicalSolutionT` (`Section3/T11/…`, read its 13 fields). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U8** (`:125-132`), `research/T15/REPORT_{376,384,421,439}.md`
(439's "the chart lands in the closed cube ⇒ pointwise equality" observation, on lane 439's branch — describe, do not import), `paper/sections/03-torus.tex:101-140` (`prop:scaling`), and the top 40 lines of
`logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first (`lake build <module>`), never assume `.olean`s exist.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T15/Equation.lean` (namespace `NSFormalization.Section3.T15`): over the raw packet clauses of `scalingStatement` and a `place : PlacementData u p f K`, for
`ε ∈ Ioc 0 place.ε₀`: (1) `periodized_momentum` — `∀ t ∈ Ioo 0 place.T, ∀ x, navierStokesResidual ν (periodizedScaledVelocity …) (normalizedScaledPressure …) t x = periodizedScaledForce … (t,x)` (the
exact spelling the T11 `ClassicalSolutionT.momentum` field uses at the **unchanged** `ν`); (2) `periodized_divergence` — `∀ t ∈ Ico 0 place.T, ∀ x, spatialDivergence (periodizedScaledVelocity …) t x = 0`;
(3) `periodized_initial` — `periodizedScaledVelocity … (0, x) = 0` (pre-activation zero past: `eps_time` gives `ε² < T`). Route: the ℝ³ scaled fields satisfy the equation (Section 4 canonical
`scaled_equation`/`scaled_divergence_free` at the source time `< 1`); periodization commutes with every operator in `navierStokesResidual` (`temporalDerivative`, `spatialLaplacian`, `advection`,
`pressureGradient`) because near any point only finitely many lattice translates are nonzero and each translate is a translate of a smooth field (`periodize_locally_eq_sum` + `contDiffOn_periodize`;
derivative of a locally finite sum = sum of derivatives; the nonlinear term: on a neighbourhood of `(t, x)` the periodized velocity equals ONE translate (single copy inside the cube + lattice shift),
so `(u·∇)u` for the periodization equals the translate's `(u·∇)u`); `normalizedScaledPressure` differs from the periodized pressure by a spatial constant (mean), so its gradient is unchanged
(T11 normalization lemma / lane 433's `pressureGradient_normalizePressureT` on lane 433's branch — reprove if absent). Deliverables: the module, `research/T15/probes/equation_closes.lean` (the three
theorems instantiated on the concrete nonzero packet of `research/T15/probes/energy_mixed_closes.lean` if reachable, else on `placement_closes.lean`'s instance), `research/T15/axioms_u8.lean`,
`research/T15/ATTEMPTS_U8.md`, U8 status line in `T15_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Equation` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_446.md`.
