# Lane 373-T17-U2-transport — T17 U2: the concrete correction data (T16's witness) and the force-operator transport `correctionForce ν v (correctionData …) ε = latticeLift (Source.correctionForce ν v (physicalCorrection …))`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/373-T17-U2-transport` (git branch `erenup/373-T17-U2-transport`, based on `origin/erenup/integration-section3` after #330, which contains
`Section3/T16/{LocalPotential,BallPotential,LatticeLift,Assembly}.lean` (`localPotentialData`, `localPotentialAPI`, `localPotential`, `latticeLift`, `spatialDivergence_translate`,
`isPeriodicOn_sub_latticeVector`, …)). Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U2 (and U5–U11: everything downstream rewrites through this unit)**,
`research/T17/Spec.lean` (`correctionForce` — the T17 spelling of `eq:H`: `∂ₜw − ν•Δw + Dw(v) + Dv(w) + advection w` with `(v·∇)w` third and `(w·∇)v` fourth — and the
`CorrectionAPI` parameters `place : PlacementData P`, `D : CutoffData`, the `reference_periodic` hypothesis `IsPeriodicOn univ v`), `research/T17/RECONCILIATION.md` §3,
the Section 4 force operator `Source.correctionForce` (grep `formalization/NSFormalization/Source/` and `Section4/I02/Reference.lean` for `correctionForce`, `correctionForce_congr_slice`),
the local operators (`temporalDerivative`, `spatialLaplacian`, `spatialDerivative`, `advection` in `Contracts`-free upstream spellings — `NavierStokes.ProblemStatement`), and the
top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** Honest partial with the exact residual statement and error text beats a stub.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T16`, `Source/`, `Section4/I02`, `Paper1/Correction*.lean`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T17/Transport.lean` (namespace `NSFormalization.Section3.T17`):
(a) `def correctionData (v : SpaceTimeField) (place …) (θ η O θR ε₀ …) : CutoffData` — T16's witness re-run (`localPotentialData v place.x₀ place.T θ η O θR ε₀` or the exact argument
    shape `Assembly.lean` uses; if `PlacementData` has no canonical module yet — lane 362 is in progress — take `x₀ T` as plain arguments and state the `place` form as a corollary once
    `place.x₀`/`place.T` are just projections), with `correctionData_correction : (correctionData …).correction ε = latticeLift (physicalCorrection v x₀ T θ η ε)` by `rfl`;
(b) restate the T17 `correctionForce` (copy the Spec's `def` verbatim into the module — only the namespace changes; docstring cites `03-torus.tex:219-223`) and prove
    `theorem force_eq (hv : IsPeriodicOn univ v) … : correctionForce ν v (correctionData …) ε = latticeLift (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))`
    (pointwise equality of space-time fields; if the two spellings differ by the order of the two middle summands, `add_comm`/`add_left_comm` after unfolding). Route: `latticeLift` is
    locally a single translate (T16 `latticeLift_eq_of_ball`, or the vendor `periodize_locally_eq_sum`), every operator in the force is local (a derivative at a point or a product at a
    point), and each translate commutes with the operators because `v` is periodic (`isPeriodicOn_sub_latticeVector`) and the operators are translation-equivariant
    (`spatialDivergence_translate` is the T16 model; prove the analogues for `temporalDerivative`, `spatialLaplacian`, `spatialDerivative`, `advection`); then the lift of a sum is the sum of
    lifts (finite sums locally; `tsum_add` with summability from local finiteness, or reduce to the single nearby copy).
(c) the periodicity of `correctionForce … ε` (`IsPeriodicOn univ`) as a corollary (lift of anything is periodic: T16 `latticeLift_periodic`).

## Deliverables
1. `Section3/T17/Transport.lean`; 2. probe `research/T17/probes/transport_closes.lean` (instantiate at a nonzero constant divergence-free `v` with T16's cutoffs; check
`correctionData_correction` by `rfl`); 3. `research/T17/ATTEMPTS_U2.md`, `research/T17/axioms_u2.lean`, status in `research/T17/T17_SPLIT.md` U2, report `research/T17/REPORT_373.md`
(if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.Transport` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
