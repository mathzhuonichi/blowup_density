# T17 split addendum — U13

- **U13 / lane 460 continuation — complete.** `SlabBridge2.lean` proves
  `correctionStatementSlab'_holds : correctionStatementSlab'`, keeping global
  periodicity and requiring only open-slab smoothness. All 45 fields close.
  The classical zero-extension probe closes by `exact`; no V2 is required
  for this statement. See `REPORT_460b.md` for the field audit and gates.

Historical first statement (retained as a negative regression):

- **U13 / lane 460 — disproved as stated.** `SlabBridge.lean` proves
  `not_correctionStatementSlab : ¬ correctionStatementSlab` for the exact
  requested block. Residual: the unchanged `reference_periodic` field requires
  global periodicity of the original reference, which slab hypotheses cannot
  imply. A T17 V2 (slab-relative reference periodicity) or an extended-reference
  conclusion is needed. Neither analytic cutoff route repairs this field.
  Build and axiom audit pass; see REPORT_460.md for gates and scope.

The continuation updates this explicitly requested U13 record;
`T17_SPLIT.md` is not modified.
