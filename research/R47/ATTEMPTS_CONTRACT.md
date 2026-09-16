# R47 V1 contract registration notes

## Successful route

- Copied the complete `RGridFamily` and `RGridAPI` declarations from
  `research/R47/Spec.lean` into `Contracts/V1/GridObservations.lean`, changing
  only the registry-conventional names to `GridFamilyAPI` and
  `GridObservationsAPI`. The contract imports only `Contracts.V1.Data`.
- Instantiated lane 258's `rGrid_choose_of_realization` with lane 255's
  unconditional `I03.compactHomogeneousRealization`.
- Transported the returned family record field by field into the public
  contract record. All field types elaborate directly; no mathematical
  rewriting, strengthened hypothesis, weakened conclusion, or norm bridge is
  needed.
- Registered `R47.grid_observations` version 1, added it to the R47 work item,
  and regenerated the task cards.

## Nominal structure boundary

The lane-258 assembly intentionally copied the research specification before
the V1 contract existed. Consequently
`Research.R47.Draft.RGridFamily` and
`Contracts.V1.GridObservations.GridFamilyAPI` are distinct inductive types,
even though their parameters and fields agree. A literal assignment

```lean
{ choose := rGrid_choose_of_realization compactHomogeneousRealization }
```

cannot have the registered result type across that nominal boundary. The
binding therefore uses `gridFamilyAPI_of_rGridFamily`, the direct analogue of
the repository's documented `ClassicalSolutionR` structure exception. Its
nineteen assignments are projections of the same lane-258 witness; in
particular, it does not select a second force family, solution family, ball,
cell, or pressure gauge.

## Scope deliberately not added

- no completed-space density assertion from Proposition 4.6;
- no point or pressure observation equality;
- no closure/interior strengthening of the common-ball containment;
- no uniformity under arbitrary refinement;
- no identification of `mixedLebesgueENorm 1 2` with an order-zero Sobolev
  norm.

The force convergence field retains the manuscript-literal
`mixedLebesgueENorm 1 2` spelling from the reconciled specification.
