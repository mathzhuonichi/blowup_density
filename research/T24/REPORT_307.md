# REPORT_307

## 1. Proposition covered

Draft B records the three Section 3 further-construction propositions:
`prop:affine`, `prop:multiple`, and `prop:conservative` (`03-torus.tex:668–740`).

## 2. Lean result

`research/T24/DraftB.lean` now contains the copied T10 solution/lifespan and
energy vocabulary, the T14 packet and T15 scaling bindings, and elaborating
`AffineVariationAPI`, `MultipleRegionsAPI`, and the Prop-valued
`ConservativeForcingAPI`.  Formulae use concrete periodic fields, force-class
membership, support hypotheses, and finite-norm guards.

## 3. Remaining gaps

This is a statements-only lane: the affine expansion/support lemmas, separated
finite-sum PDE/energy proof, conservative integration-by-parts proof, and the
bounded-domain branch remain unproved.  They are listed in
`COMPARISON_B.md`.

## 4. Verification

Command run:

`cd verification && lake env lean ../research/T24/DraftB.lean`

Result: success with no errors or warnings; no `sorry` or placeholder
declarations.
