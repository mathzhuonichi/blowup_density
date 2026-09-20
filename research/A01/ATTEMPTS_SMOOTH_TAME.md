# Lane 206 — smooth cylinder tame attempts (partial)

## Checkout and descent audit

The starting commit is `09ecf46` (lane 205). Contrary to the task's integration
snapshot, this checkout has no `Section4/A01/SignedPassage.lean`. Its envelope
row and `RootComparison.lean` still retain `CylinderSignedRootLimit`. No merge,
rebase, fetch, or change to existing Lean modules was performed to repair that
snapshot discrepancy. An unconditional constructor cannot be claimed here.

Read CLAUDE, HANDOFF §0/§2 P7, NEXT_SESSION, LESSONS first 40 lines, REPORT_205,
ATTEMPTS_COORDINATE_TAME, ATTEMPTS_COMMUTATOR_BOUND, REVIEW_200 §3, the three
finite forcing modules, A03 scalar/outer product statements, L2Descent,
DatumPathContinuous, CylinderWiring, MildUniqueness, and the vendor ordinary
interpolation, tame product, cylinder embedding and word-block sources.

Consumer-by-consumer:

* `CylinderCoordinateTame` quantifies over **all** compatible finite cylinder
  pairs. `cylinderCommutator_le` only needs the coordinate inequalities at the
  particular pair, but its present premise is universal. An invariant-only
  estimate does not inhabit that premise.
* `cylinderCoordinateTame` uses unrestricted smooth density. An invariant
  recut requires invariant-preserving approximants, not merely adding an
  invariance binder to the smooth premise.
* `ForcingFamilyBound` quantifies over arbitrary Duhamel fixed points and
  their maximal limits, without an invariance binder. `forcingFamilyBound_of_cylinder`
  applies its input to `(extendPath u r, U r)` almost everywhere. One must
  establish invariance at that application point before using descent.
* `CylinderWiring.hpairs` supplies invariance for the constructed tower, but
  that construction already consumes the all-order bounds. It cannot by
  itself supply invariance of arbitrary competitors while proving those bounds.
* `MildUniqueness.quadratic_mild_unique`, translation-equivariance in
  `Source/ForcedCylinderTranslation`, and invariant existence in
  `Source/ForcedCylinderInvariant` are plausible ingredients for the recut.
  This lane does not claim such a recut impossible, or completed.
* `word_descent_ae_top/full` handle every **spatial** word order but require
  invariant data and, for the classical identity, an ordinary smooth
  representative. They do not identify arbitrary angular-dependent fields
  with ordinary fields. No invariant predicate/transfer is exported here.

## Proved fallback progress

`SmoothTame.lean` transplants the interpolation argument to genuine finite
cylinder arrays. The strengthened integration-by-parts estimate retains the
actual higher word, instead of bounding it by the ambient norm as in vendor
`word_square_le_parent`. It gives finite-interval log-convexity. Cross, pair,
and between inequalities are proved without assuming log-convexity beyond
available order; the maximum's zero extension is never used as a globally
log-convex sequence.

`cylinderWordMaximum_product_le` gives constant-one interpolation at arbitrary
low order. `cylinderWordMaximum_le_gradient` identifies each positive word
with an actual entry in the exact full gradient array. Consequently
`cylinderWordMaximum_product_le_gradient` has exactly the target low-order-seven
factor and full gradient factor, with constant one, including angular words.

`cylinderMixedProduct_left` is an actual L² scalar-vector product bound, not
just a product of L² norms. The coefficient is the genuine H³ word block;
`scalarProduct` is the vendor's L² class of its pointwise product. Using its
proved H³ embedding, all three extra derivative orders fit in the low-order
seven interpolation budget. Its constant is exactly
`‖L‖ * sobolevEmbeddingConstant 1 3`. This certifies that restricted product
estimate, NOT a general coordinate commutator constant.

## Negative examples and remaining work

* A spatial bump times a nonconstant smooth periodic angular function cannot
  be identified with an ordinary lift. This is a mathematical scope example,
  not a Lean formalized counterexample.
* A product of L² norms does not bound the L² norm of a pointwise product:
  concentrated L²-normalized bumps have unbounded product L² norms. The
  actual mixed-product theorem therefore explicitly uses three embedding
  derivatives; it never makes this invalid inference.
* If the coefficient word is near top order, `3+a ≤ 2+q` fails. The theorem
  `cylinderMixedProduct_left` alone cannot cover those Leibniz leaves; a
  bound using the transported factor's embedding margin is still required.
* The scalar product theorem does not identify the finite commutator with
  the smooth Leibniz expansion. That assembly and its combinatorial constant
  remain unproved. No zero example is used to certify a universal premise.

The single existing named analytic input is still
`SmoothCylinderCoordinateTame q hq C`, exactly as stated in REPORT_206 §3.
No second analytic hypothesis or new logical assumption has been introduced.
This delivery is **partial**, not closure of the requested fallback or A3-M2.

## Diagnostics (resolved unless noted)

Initial log-convexity proof rewrote `Fin.cons_self_tail` also inside the higher
word. The subsequent bound needed `Fin.cons (w 0) w`, not the unreduced nested
cons. Lean reported `Application type mismatch` with those two word indices.

A copied cross calculation used the wrong multiplication side for
`mul_le_mul_iff_right₀`; Lean reported `invalid 'calc' step, left-hand side is`
`x (a + 1) * x (a + d.succ) * x (a + d)` but expected
`x (a + d) * (x (a + 1) * x (a + d.succ))`. Reordering the calculation fixed it.

Untyped nested `single_le_sum` calls in the gradient proof produced:
`(deterministic) timeout at whnf, maximum number of heartbeats (400000) has been reached`.
Explicitly typing the squared-norm array and the inner/outer sum comparisons
resolved it within the permitted declaration-local 400000 setting.
Deprecated `dif_pos` was replaced with `dite_eq_left` for zero diagnostics.

The missing source is a checkout fact (not a Lean mathematical error):
`rg: formalization/NSFormalization/Section4/A01/SignedPassage.lean: No such file or directory`.
No failed Lean proof of the full analytic target is being presented as a
proof of impossibility. Final commands/results are in REPORT_206.
