# Lane 205 — coordinate tame estimate

## Scope and analytic status

Partial delivery under the satisfiability rule. No unconditional uniform
coordinate Kato–Ponce constant is proved. The one named analytic hypothesis is
`SmoothCylinderCoordinateTame q hq C` in `CoordinateTame.lean`. It requires the
exact lane-202 inequality only for finite elements admitting an actual smooth
cylinder representative with all derivative words in L². It includes angular
dependence. It is not an ordinary-lift hypothesis.

The target `cylinderCoordinateTame_exists` is explicitly conditional on
`∃ C, SmoothCylinderCoordinateTame q hq C`; it must not be reported as the
requested unconditional existential. The equivalence with
`CylinderCoordinateTame` establishes that the restriction to smooth elements
loses neither generality nor any part of the desired constant.

## Positive route

* `cylinderLeibniz` recursively assigns each derivative to either factor.
  Its equality theorem proves the full expansion into mixed scalar-vector
  products on smooth cylinder fields.
* `cylinderCommutatorLeibniz` removes the branch with no coefficient
  derivative. Its equality theorem follows the actual scalar commutator
  recurrence. When the second field is already a coordinate derivative,
  both factors of every surviving mixed product have a derivative.
* `cylinderCoordinateLeibniz_sign` verifies transport-minus-product is the
  negative of this expansion, using commutation of smooth coordinate words.
  This is a smooth-field identity; an a.e. identification of every finite
  product word with this expansion is not claimed here.
* The finite coordinate commutator and exact full gradient word norm are
  continuous at the stated orders. `EulerSmoothInequalityTransfer.binary_le_of_smooth`
  supplies actual heat/mollifier approximations with smooth H-infinity
  representatives. Both functionals depend only on its first input; the
  lower field is always the restriction of that same higher field.
  Compatibility is therefore preserved exactly, and the finite-order limit
  passage requires no additional hypothesis or derivative loss.
* `coordinateTameA q C := max (A q) (C/4)`. The proved arithmetic comparison
  is `C ≤ 4 * coordinateTameA q C`; summing four coordinates gives lane 200's
  factor sixteen. The generalized forcing composition uses lane 200's
  unaltered `ForcingFamilyBound` predicate with this enlarged constant.
  No assumption `C ≤ 4*A q` is made in that composition.

## Why the analytic core remains

The requested sources were read, including REPORT_202 §3, the lane-200 review
§3, `AsymmetricTransport`, `TransportL2Time`, `fieldDerivative_smul`,
`scalarCommutator_recurrence`, `word_derivative_comm`, `transportCommutator_eq_sum`,
`coordinateProduct_tame`, `tame_outer_product`, and `wordMaximum_product_le`.
No REVIEW_202 file was present in this checkout.

Searches of Section4 D01/A03/A04/A01/C01 and the vendor cylinder/word/product
modules located these closest interfaces:

* OrdinaryWordInterpolation uses `SmoothL2Field Space` and Fin 3 words;
  OrdinaryTameProduct has the same carrier. Its log-convexity/pointwise
  product argument is a plausible transplant, not a theorem applicable by
  coercion to these Fin 4 cylinder fields.
* A03 `tameProductScalar` (ScalarTameProduct:254) and `outerProductTame`
  (OuterTameProduct:177) concern physical R³ Sobolev data and their ENNReal
  norms. They do not give the present mixed cylinder-word estimate directly.
* `SobolevInterpolation.word_square_le_parent` proves a genuine cylinder
  integration-by-parts estimate, but bounds its high factor by the full
  ambient Sobolev norm. A sharp word-maximum product interpolation and its
  mixed-product embedding/gradient comparison still need development.
* `BaseTransportCommutator.scalarCommutator_bound` only covers word order
  at most six, whereas the target includes order q+1, at least seven.
* `asymmetricTransport_bound` has high norm times high norm and does not
  supply the fixed order-seven low factor. Restriction estimates point the
  wrong way for that substitution.

No angular-invariant recut is made. An ordinary estimate cannot be applied
to all cylinder elements: a spatial bump times a nonconstant smooth periodic
angular function is outside the ordinary-lift subspace. Restricting the
predicate to invariant fields would also require proving invariance of the
actual maximal-limit representatives at the application point in lane 200,
not just quoting invariance of lane 192's chosen tower.

The residual smooth hypothesis retains the original finite products, so it
also retains their smooth-word identification obligation. We do not claim
the separate smooth Leibniz theorem alone discharges that obligation. Zero
examples verify actual compatible data but do not prove satisfiability of
the universally quantified estimate on all nonzero fields. Both sides have
quadratic amplitude scaling; the low norm has not been squared.

## Elaboration diagnostics

Initial nested continuity proofs triggered `failed to synthesize AddCommMonoid`
and `timeout at whnf` at the allowed heartbeat limit. A minimal probe showed
that an untyped intermediate `(derivativeOperator ...).continuous` caused
expensive inference whereas an explicitly typed `Continuous (...)` proof
succeeded. Intermediate map types are therefore stated explicitly. Local irreducibility
for the two bounded product maps and the coordinate commutator prevents
unification from unfolding their analytic constructions. No
heartbeat setting above 400000 is used. Final gate results are in REPORT_205.
