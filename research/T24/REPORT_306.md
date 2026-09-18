# Report 306

## Implemented
Completed `research/T24/DraftA.lean` with the copied T10/T14/T15 vocabulary and three clause-indexed APIs: `AffineVariationAPI`, `MultipleRegionsAPI`, and `ConservativeForcingAPI`.

## Validation
`cd verification && lake env lean ../research/T24/DraftA.lean` succeeds.

## Deliverables
Added `COMPARISON_A.md` with a paper-clause to field table, ambiguities, lemma needs, and implementation candidates.

## Limits
The APIs are statement-only interfaces: each paper clause is represented as its own proposition field, with concrete construction proofs deferred to later implementation work.
