# A01 V2 contract-registration attempts

Lane 212 registers the already proved local theory from lane 211.  No new
analytic theorem is introduced here; the work is the exact contract boundary,
the implementation binding, and adversarial non-vacuity/conformance checks.

## 1. Contract shape and the deliberate narrowing

The frozen V1 API `ManuscriptLocalRegularityPartialAPI` already owns the two
arbitrary-solution clauses `projected` and `pressure_potential`.  V2 therefore
extends it structurally and adds:

- a named real `horizon`;
- a `ClassicalSolutionR` on that horizon for every positive viscosity,
  `initialClassR` datum, and `MemForceR` force;
- the full four-field `ManuscriptLocalRegularity`, copied from
  `research/A01/Spec.lean:167-230` for that exact solution and horizon;
- the owner-approved quantitative field with the force fixed before `∃ δ` and
  an H⁷ datum bound.

The paper/draft H¹ statement is not a structure field.  It is retained as
`ManuscriptHorizonLowerBoundH1 api : Prop`, with the draft quantifier order and
norms, and is explicitly documented as open and not implied by V2.  The exact
difference is substantive: the draft chooses `δ` before both datum and force
and uses H¹/`L¹_tH¹_x` bounds; V2 chooses it after fixing the force and bounds
the datum in H⁷.  A04's additional uniformity over restart times and the shifted
copies of one force is proved separately in lane 215, not asserted by this
contract field.

## 2. Binding and conversion attempts

The direct successful binding uses lane 211's `localHorizon'`, `localCarrier`,
`manuscriptLocalRegularity_localCarrier`, and
`horizon_lower_bound_H7_fixedForce`.  The contract-side copies of
`convectionDivergence`, `HasSymmetricJacobian`, `IsLerayComplement`, the radial
pressure potential, and `sobolevENorm` each have an explicit `rfl` bridge.

`ClassicalSolutionR` is the permitted structure exception at the contract
boundary.  The implementation uses the A02 structure, so the binding goes
field by field through `uniqueness_toA02` and `maximalPartial_ofA02`, following
`Section4/A02/Restrict.lean` §0.  Both full-structure round trips are proved by
case analysis and `rfl`; the regularity record is then transported field by
field.  This avoids any assertion that two independently declared structures
are definitionally identical.

An attempted import of the frozen `Bindings.RegularityPartial` alongside the
lane-211 regularity assembly is not viable: its older dependency path and
`ManuscriptRegularity.lean` export the same implementation theorem name
`projected_of_classicalSolution`.  V2 instead fills the inherited fields with
the same implementation theorems and exports
`regularityPartial_of_v2 := localTheoryV2.toManuscriptLocalRegularityPartialAPI`.
The frozen V1 binding and tests are unchanged.

## 3. Non-vacuity and mutation checks

`axioms_contract_v2.lean` constructs a nonzero compact smooth force from time
and space bumps and proves it is in `MemForceR`.  It independently constructs
a nonzero compactly supported solenoidal datum as the curl of a cutoff linear
potential and proves membership in `initialClassR` and finiteness of its H⁷
norm.  The examples then:

1. obtain the selected classical solution at those two nonzero inputs and read
   its positive horizon; and
2. instantiate `horizon_lower_bound` at the same force and datum to obtain a
   real `δ` with both `0 < δ` and `δ ≤ horizon …`.

Thus neither the input classes nor the positive conclusion are exercised only
through zero or inconsistent hypotheses.  The mutation suite targets this V2
field directly: a fabricated lower-bound axiom is rejected as an extra axiom,
and removing `MemForceR f` is rejected as a weakened-hypothesis mutation.

## 4. Registry accounting

The task text expected `registered_contracts: 30`, but the actual base
`origin/erenup/integration` already contains 32 registered contracts, ending
with `R41.main_thresholds`.  The additions-only A01 V2 entry therefore makes
the honest result 33.  No existing registry entry was removed or rewritten to
manufacture the stale count.  JSON was written with Unicode preserved and
two-space indentation, and the generated task views were refreshed from
`collaboration/work_items.json`.
