# T12 U2 cutoff attempts (lane 365)

## Route used

The cutoff is a fixed `ContDiffBump (0 : Space)` with `rIn = 5/2` and
`rOut = 3`. The fundamental cube is contained in the radius-two ball by the
`PiLp.norm_sq_eq_of_L2` identity and the elementary coordinate bounds
`0 ≤ x i ≤ 1`. Thus the bump is identically one on the whole cube and on a
neighborhood of each cube point. Its topological support is the closed
radius-three ball, which is contained in the open radius-four ball chosen as
`largerCube`.

The open plateau is exported as `cutoff_eq_one_on_ball`, so downstream
localization arguments can use equality on a neighborhood rather than only the
closed cube restriction.

Derivative bounds use the compact-support route intended by U2:
`ContDiff.continuous_fderiv` / `ContDiff.continuous_iteratedFDeriv`,
`HasCompactSupport.fderiv` / `HasCompactSupport.iteratedFDeriv`, and
`Continuous.bounded_above_of_compact_support`. Vanishing of the first and
second derivatives on the cube follows by differentiating the neighborhood
equality to the constant one (`EventuallyEq.fderiv_eq` and
`EventuallyEq.iteratedFDeriv`). For `cutoffMul`, pointwise scalar smoothness,
`HasCompactSupport.smul_right`, and
`D01.memHInfty_of_contDiff_memLp` close the product and `MemHInfty` clauses.

## Alternatives rejected

* A coordinate-product cutoff would require three separate one-dimensional
  bump functions and a longer support/range calculation. The Euclidean bump
  has the same fixed enlargement property and keeps the proof independent of
  coordinate product lemmas.
* `exists_contDiff_tsupport_subset` only produces a bump equal to one at one
  point. The compact-cube plateau is instead supplied directly by the fixed
  `ContDiffBump` radius.
* A named analytic proposition input was unnecessary; all obligations close
  from Mathlib and the existing D01 conversion theorem.

## Elaboration issues resolved

1. `Finset.sum_le_sum` does not infer `Finset.univ` from a binderless finite
   sum. The proof was changed to a `calc` through `∑ i : Fin 3, (1 : ℝ)`.
2. The norm-square bound needs the explicit nonnegative product
   `0 ≤ x i * (1 - x i)`; `nlinarith` does not invent that product from
   `0 ≤ x i ≤ 1`.
3. `interior` is discharged with `Metric.isOpen_ball.interior_eq`; the cutoff
   support is first unfolded from `cutoff` to the coercion of `cutoffBump`.
4. `HasCompactSupport.fderiv` has an explicit scalar-field argument, so the
   call is `HasCompactSupport.fderiv ℝ hasCompactSupport_cutoff`.
5. The second derivative of a constant is exposed by two applications of
   `iteratedFDeriv_succ_eq_comp_left`, with an intermediate constant-zero
   derivative proved via `fderiv_const`.

No `sorry`, `admit`, `axiom`, `native_decide`, or heartbeat override is used.
