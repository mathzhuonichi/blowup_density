# R45 compact-class proof notes (lane 252)

## Successful route

- `MemForceCompact` closure uses the registered
  `datumLemmas.memForceCompact_add` on `(f - g) + g`, followed by function
  extensionality and `sub_add_cancel`.
- `F_c ⊆ F_R` needs no new hypothesis: it is exactly the registered
  `datumLemmas.memForceCompact_memForceR` field, proved upstream by
  `Section4/D01/ForceClass.lean`.
- `density_compact` follows lane 235's two cases.  In the insertion case,
  `forceDifference_compact` and compact addition closure put the inserted
  force back in `F_c`; the same R42 record gives exact lifespan and force-norm
  convergence.
- For `zeroIff_compact`, the reverse implication is `density_compact` at the
  zero datum.  The forward implication uses lane 232's
  `R41.nonDensityZero_of_q`, whose explicit positive excluded radius is
  centered at zero.  A compact breakdown witness is transported to the
  registered `F_R` breakdown set using `F_c ⊆ F_R` and lane 249's lifespan-set
  bridge.

## Rejected or repaired routes

1. Applying `mainThresholds_nonDensity` directly is insufficient.  Its
   conclusion is the negation of relative density for all targets in `F_R`;
   relative density only in `F_c` does not imply that stronger proposition.
   The explicit excluded ball from `nonDensityZero_of_q` is the required
   monotone statement.
2. Simplifying `MemForceCompact ((f - g) + g)` directly did not rewrite under
   the predicate.  An explicit equality of functions, then `rw`, closes the
   transport without adding an extensionality lemma.
3. The formalization-side `R41.breakdownSetRZero` and force norm are restated
   definitions.  They are transported through lane 249's
   `mainThresholds_breakdownSetR_eq` and
   `mainThresholds_forceSobolevENorm_eq`; treating them as syntactically
   identical fails elaboration.

No class fact remains isolated as a hypothesis, so lane 234 owes this compact
subcase nothing.  Its rapid-class closure facts are still needed for the
`Y = forceClassRapid` instances.
