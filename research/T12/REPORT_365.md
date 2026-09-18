# REPORT — lane 365 (`365-T12-U2-cutoff`)

## 1. What was proved

T12 U2 is closed. The new module constructs a fixed smooth cutoff
`cutoff : Space → ℝ` from `ContDiffBump (0 : Space)` with plateau radius `5/2`
and support radius `3`. The documented `largerCube` is the open Euclidean ball
`Metric.ball 0 4`, a convenient fixed enlargement containing the fundamental
cube and the closed support ball. The module proves:

* `cutoff_contDiff`, `cutoff_eq_one_on_ball` on an open plateau containing the
  cube, `cutoff_eq_one` on `fundamentalCube`, and
  `cutoff_range : ∀ x, cutoff x ∈ Icc 0 1`;
* `tsupport_cutoff ⊆ interior largerCube` and
  `hasCompactSupport_cutoff`;
* the same interior support inclusion for the first and second derivatives;
* finite global bounds for `‖fderiv ℝ cutoff x‖` and
  `‖iteratedFDeriv ℝ 2 cutoff x‖`;
* `fderiv ℝ cutoff` and `iteratedFDeriv ℝ 2 cutoff` vanish on the fundamental
  cube, using the plateau neighborhood rather than only pointwise equality;
* `cutoffMul`, its smoothness and compact support, exact agreement with the
  original field on the cube, and `memHInfty_cutoffMul` from smoothness plus
  compactly supported jets.

The probe `cutoff_closes.lean` instantiates `cutoffMul` on the same finite
two-mode Fourier coefficient pattern used by `tame_product_closes.lean`, puts
the real scalar in all three vector components, and closes the cube equality by
`simp`.

## 2. What is in Lean now

* `formalization/NSFormalization/Section3/T12/Cutoff.lean` (namespace
  `NSFormalization.Section3.T12`), 198 lines, no placeholders or extra named
  proposition inputs.
* `research/T12/probes/cutoff_closes.lean`, 46 lines.
* `research/T12/axioms_cutoff.lean`, auditing all 23 public declarations.
* `research/T12/ATTEMPTS_CUTOFF.md`, documenting the construction and resolved
  elaboration issues.
* U2 status is marked complete in `research/T12/T12_SPLIT.md`.

Every audited declaration reports exactly `[propext, Classical.choice,
Quot.sound]`.

## 3. Gaps and design notes

The enlargement is a Euclidean ball rather than a coordinate cube; this is an
intentional documented choice that makes the standard `ContDiffBump` support
calculation immediate. The radius-four open ball is strictly larger than the
radius-three closed support and contains the unit cube. The first- and
second-derivative support lemmas explicitly place those supports in the shell
`interior largerCube \ fundamentalCube`; downstream U3/U5 can also use the
open plateau, cube vanishing, compact support, and global derivative bounds.

No residual theorem or named input remains in U2. The later analytic units U3,
U4, U5, and U6 remain outside this lane.

## 4. Commands and results

From the worktree root, after `. scripts/lean-env.sh`:

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.Cutoff`
  — PASS, 0 errors.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T12/Cutoff.lean`
  — PASS, silent.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/cutoff_closes.lean`
  — PASS, silent.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T12/axioms_cutoff.lean`
  — PASS; all 23 declarations report exactly the standard three axioms.
* `make check` — PASS (architecture and contract-policy checks).
