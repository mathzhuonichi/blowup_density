# Lane 468-T24-Ub4-assembled-solution — T24b Ub4: the assembled multi-region classical solution (`assembled_*`, `solution`, `solution_pin`, `force_mem`, `rest`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/468-T24-Ub4-assembled-solution` (git branch `erenup/468-T24-Ub4-assembled-solution`, = lane 467's branch (in review) + `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T24/T24_SPLIT.md`** (§0; §1 T24b unit Ub4 verbatim, ⑦ in `research/T24/RECONCILIATION.md` §4), `research/T24/REPORT_467.md` + `Section3/T24/Multiple.lean` (canonical `MultipleRegionsAPI`, 30 fields; `finiteVelocitySum/PressureSum/ForceSum`,
`SpeedUnboundedAtOn`; the exact field statements `assembled_velocity_formula`, `assembled_pressure_formula`, `assembled_force_formula`, `solution : ClassicalSolutionT ν 0 assembled_force T`, `solution_pin`, `force_mem`, `rest`) and
`Section3/T24/MultipleComponents.lean` (`RegionsData` — raw packet + clauses, `T`, `N`, regions, `regions_disjoint`, `region_interior`; `placement j`, `scaling j`, `ε j`, `component j : ClassicalSolutionT ν 0 F_j T`, `component_pin`, `component_support`
(velocity slices vanish on `fundamentalCube ∖ B_j`), `component_force_support`), `Section3/T15/Solution.lean` (how the single-packet `ClassicalSolutionT` was assembled: which fields need what), `verification/Contracts/V1/TorusLocalTheory.lean:130-200`
(`ClassicalSolutionT` fields: `velocity_smooth`, `pressure_smooth`, `initial`, `divergence`, `momentum`, `sobolev`, `pressure_gradient`, `velocity_periodic`, `pressure_periodic`, …), `Section3/T10`/`T11` for `forceClassT` and its closure under finite sums
(grep `forceClassT` lemmas: smoothness, periodicity, compact positive-time support, zero-mean gauge — check what `forceClassT` actually requires), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T24.MultipleComponents`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T24/MultipleAssembled.lean` (namespace `NSFormalization.Section3.T24`, `namespace RegionsData`, variable `d : RegionsData ν u p f K M E`):
- `def assembledVelocity d := finiteVelocitySum (fun j ↦ (d.component j).velocity)`, `assembledPressure`, `assembledForce := finiteForceSum (fun j ↦ periodizedScaledForce f (d.placement j).x₀ d.T (d.ε j))` with the three `*_formula` theorems by `rfl`.
- **`def solution d : ClassicalSolutionT ν (0 : SpatialField) d.assembledForce d.T`** — the hard core (⑦): each `ClassicalSolutionT` field for the finite sum. Linear fields (smoothness, periodicity, initial value `rest`, divergence, Sobolev paths, pressure gradient
  bounds) are finite sums of the components' fields. The momentum equation needs the **cross terms to vanish**: `(U_i·∇)U_j = 0` for `i ≠ j` because on `fundamentalCube` the velocity slices have disjoint supports (`component_support` + `regions_disjoint`)
  and everything is unit-periodic (`velocity_periodic` on `Ico 0 T`) — so at every `x` at most one component is nonzero *in a neighbourhood* (support is closed: use `tsupport` disjointness to get a neighbourhood where the others vanish, then
  `fderiv` of a locally-zero function is zero) — spell this out as a lemma `crossTransport_eq_zero`. Then the nonlinear residual of the sum equals the sum of the residuals (pressure and force are linear). Mind the exact spelling of the registered
  `navierStokesResidual`/momentum field (advection term first or `Dv(w)` order) — copy it from `ClassicalSolutionT.momentum`.
- `theorem solution_pin : d.solution.velocity = d.assembledVelocity ∧ d.solution.pressure = d.assembledPressure` (by `rfl` if `solution` is built with those fields), `theorem force_mem : d.assembledForce ∈ forceClassT` (closure of `forceClassT` under finite
  sums: prove the general lemma `forceClassT_finset_sum` if absent), `theorem rest : ∀ x, d.assembledVelocity (0, x) = 0` (from each `component`'s `initial` at datum `0`).
- If the momentum field does not close in time, deliver every other field as separate theorems and a structure-valued theorem is NOT acceptable as a substitute for `solution`; state the exact residual (the cross-transport lemma or the specific
  field) with its error text.
Deliverables: the module, `research/T24/probes/assembled_closes.lean` (fields by `exact` against `Multiple.lean`'s statements instantiated at `d`), `research/T24/axioms_ub4.lean`, `research/T24/ATTEMPTS_UB4.md`, Ub4 status line in `T24_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.MultipleAssembled` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (statements / files / gaps with error text / commands and results). Also write it to `research/T24/REPORT_468.md`.
