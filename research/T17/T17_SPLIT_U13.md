# T17 split addendum — U13

- **U13 / lane 460 — disproved as stated.** `SlabBridge.lean` proves
  `not_correctionStatementSlab : ¬ correctionStatementSlab` for the exact
  requested block. Residual: the unchanged `reference_periodic` field requires
  global periodicity of the original reference, which slab hypotheses cannot
  imply. A T17 V2 (slab-relative reference periodicity) or an extended-reference
  conclusion is needed. Neither analytic cutoff route repairs this field.
  Build and axiom audit pass; see REPORT_460.md for gates and scope.

This new companion file preserves the explicit new-files-only instruction;
`T17_SPLIT.md` is not modified.
