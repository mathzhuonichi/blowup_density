# R45 rapid-class proof notes (lane 257)

## Successful route

- `density_rapid` is lane 252's lifespan case split with the two rapid class
  facts from `Section4/R41/ClassFacts.lean`.  G2 sends the target force from
  `F_rd` to `F_R`, allowing `insertionLifespanV2_of_data`; G3 combines the
  rapid target with the insertion record's compactly supported difference and
  keeps the inserted force in `F_rd`.
- `zeroIff_rapid` uses `density_rapid` for the if direction.  The only-if
  direction uses lane 232's explicit excluded ball centered at zero.  G2
  transports any rapid breakdown witness to `breakdownSetRZero`, after which
  the registered lifespan-set and force-norm bridges match the upstream
  non-density statement.
- `regularReference_rapid` follows lane 254's compact rider proof with only
  the two class steps changed to G2/G3.  One insertion record supplies exact
  lifespan, force convergence, energy convergence, and common history.  The
  existing uniqueness theorem identifies its reference velocity with the
  caller's `v` on `[0,T)`.
- `schwartzDensity` is exactly G4 followed by `density_rapid`; no additional
  `a ∈ initialClassR` premise is exposed.
- The guarded parametric `density` and `zeroIff` fields are direct case splits
  on `Y = forceClassCompact ∨ Y = forceClassRapid`, using lane 252 and this
  lane respectively.

## Rejected or repaired routes

1. The negation of ambient `F_R` relative density cannot by itself prove the
   rapid-class only-if direction: rapid density ranges over fewer target
   centers.  As in the compact template, the explicit positive excluded ball
   from `R41.nonDensityZero_of_q` is the monotone statement needed here.
2. The rider cannot be obtained by merely selecting an epsilon for force
   convergence.  Its same witness must also meet energy closeness and contain
   the caller's cutoff in the history interval.  The intersection of all four
   eventual conditions (`ε ≤ ε₀`, history window, force bound, energy bound)
   is necessary.
3. Importing `Bindings.Packet` alongside the insertion route is deliberately
   avoided because it collides with `Bindings.Scaling` on
   `navierStokesResidual_eq`.  `Bindings.CompactClassDensity` reaches
   `Bindings.InsertionFromData`, whose fresh packet assembly is the compatible
   route.
4. A first transcription accidentally used the calligraphic character `𝒜`
   in place of Lean's neighborhood notation `𝓝`; replacing the glyph restored
   the intended filters.  This was a source-level typo, not a proof gap.

No named supplier hypothesis was needed: G2, G3, and G4 all transport
definitionally through the contract-vocabulary restatements audited in
`research/R41D/axioms_class_facts.lean`.
