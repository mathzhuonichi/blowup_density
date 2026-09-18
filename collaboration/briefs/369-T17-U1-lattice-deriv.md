# Lane 369-T17-U1-lattice-deriv — T17 U1: the lattice-lift iterated-derivative bridge (`latticeLift w` is locally one translate of `w`, so all its iterated derivatives are those of the single nearby copy)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/369-T17-U1-lattice-deriv` (git branch `erenup/369-T17-U1-lattice-deriv`, based on `origin/erenup/integration-section3`, which contains
`Section3/T16/LatticeLift.lean` (#329: `latticeLift`, `latticeLift_eq_periodize` (`rfl` to the vendor `periodize`), `latticeLift_eq_of_ball :135`, `latticeLift_sliceSupport :271`,
`latticeLift_smooth`, …)). Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U1 (and U5/U6 to see how it is consumed)**, `Section3/T16/LatticeLift.lean`, the vendor
`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean` (`periodize_locally_eq_sum :136`, `periodize_eventuallyEq :252`, `contDiff_periodize :155` — the local-single-translate
facts), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T16`, `Section3/T10`, `Section4/I02`, `Paper1/Correction*.lean`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T17/LatticeDeriv.lean` (namespace `NSFormalization.Section3.T17`):
`theorem latticeLift_iteratedFDeriv_eq` — for `w : SpaceTimeField` smooth with every spatial slice supported in `ball x₀ ρ` (the hypothesis shape of `latticeLift_sliceSupport`),
`ρ < 1/2` (or the `r + ρ ≤ 1` form used in `LatticeLift.lean`; pick the one matching `latticeLift_eq_of_ball`), every `z : SpaceTime`, order `n : ℕ` and direction tuple `u`:
`‖iteratedFDeriv ℝ n (latticeLift w) z u‖ = ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖` for the one nearby copy `k` (state it existentially: `∃ k, …`, plus the `k = 0` form when
`z.2 ∈ ball x₀ ρ'`/the fundamental cube), and the corollary that `‖iteratedFDeriv ℝ n (latticeLift w) z‖ ≤ ⨆ z', ‖iteratedFDeriv ℝ n w z'‖`-type bound (state in the `ℝ≥0∞`/`⨆` spelling that
`CorrectionAPI.correction_derivative_bound` (`research/T17/Spec.lean`) uses — read it and match). Route: `latticeLift w =ᶠ[𝓝 z] fun z' => w (z' - (0, latticeVector k))` (locally a single
translate: the translated supports `ball (x₀ + latticeVector k) ρ` are pairwise disjoint and locally finite — `latticeLift_eq_of_ball` gives the identity on a ball, so on an open
neighbourhood), then `Filter.EventuallyEq.iteratedFDeriv_eq` (grep Mathlib for the exact name: `Filter.EventuallyEq.iteratedFDeriv` / `iteratedFDeriv_congr_of_eventuallyEq`) and
translation invariance of `iteratedFDeriv` (`iteratedFDeriv_comp_sub`-type lemma or `ContinuousLinearEquiv`/translation argument). Also the zero case: where no copy is near, both sides are 0.

## Deliverables
1. `Section3/T17/LatticeDeriv.lean`; 2. probe `research/T17/probes/lattice_deriv_closes.lean` (instantiate on the nonzero bump of `research/T16/probes/lattice_lift_closes.lean`; check the
`k = 0` form at a point of the cube); 3. `research/T17/ATTEMPTS_U1.md`, `research/T17/axioms_u1.lean`, status in `research/T17/T17_SPLIT.md` U1, report `research/T17/REPORT_369.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.LatticeDeriv` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T17/REPORT_369.md`.
