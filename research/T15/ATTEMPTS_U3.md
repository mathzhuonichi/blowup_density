# T15 U3 attempts — lattice summability and single copy

Lane 421, 2026-09-18.  Target: the six canonical fields
`velocity_summable`, `pressure_summable`, `force_summable`,
`velocity_singleCopy`, `pressure_singleCopy`, and `force_singleCopy` from
`Section3/T15/Scaling.lean`.

## Route that closed

1. Lane 376's three `scaled*_slice_subset_cube` theorems turn the raw packet
   support clauses plus `PlacementData` into
   `tsupport (scaled slice) ⊆ interior fundamentalCube` on exactly the time
   domains of the six fields (`t < T` for velocity/pressure, every `t` for
   force).
2. `supportedInCube_of_tsupport_subset_interior` observes that strict support
   in `[0,1]³` implies the vendor coordinate bound with radius `1`.
   `NavierStokes.PeriodicLocalization.summable_translate` then gives genuine
   pointwise summability because the translate family has finite support at
   every point.  Lane 362's bridge guarantees that this is definitionally the
   T13 lattice family.
3. `lattice_term_eq_zero_of_mem_cube` is the value-generic form of
   `T13.eq_zero_of_mem_cube`: if `x ∈ [0,1]³` and `n ≠ 0`, one coordinate of
   `x-n` lies outside `(0,1)`, so the translated value vanishes.
   `tsum_eq_single` leaves only `n=0`.  Making this lemma generic in the value
   type handles both vector velocity/force and scalar pressure.
4. Each final theorem states its `ScalingAPI` field type literally.  The six
   examples in `probes/single_copy_closes.lean` close those copied types by
   `exact`.

No named input was introduced.  The only additional premises of the six
theorems are the raw packet clauses already present before `PlacementData` in
`scalingStatement`: compactness and slice support for velocity/pressure, and
`CompactPositiveTimeSupport` for force.

## Alternatives rejected

- `T13.periodize_eq_of_mem_cube` directly closes the vector-valued velocity
  and force equalities, but its `SpatialField` specialization cannot state the
  scalar pressure equality.  A value-generic zero-translate lemma avoids
  duplicating two proof paths.
- `periodize_add_lattice` proves periodicity, not summability.  The relevant
  vendor endpoint is `summable_translate`, whose proof is built from the same
  local finite-sum mechanism as `periodize_locally_eq_sum`.
- Compact support alone could be converted to an unspecified large coordinate
  cube.  The already available strict fundamental-cube support gives the
  explicit radius `1` immediately and keeps the proof tied to placement.

## Concrete check

`probes/single_copy_closes.lean` repeats the explicit nonzero bump geometry of
`placement_closes.lean`, takes `T=1`, `ε=ε₀=1/2`, and fires all six theorems at
the active time `t=7/8` and cube centre.  Shrinking the earlier probe's
threshold from `1` to `1/2` makes `2ε²<T` true for every admissible scale and
therefore yields a full canonical `PlacementData`.  The force is the zero
field (with honest compact positive-time support), while the velocity slice is
separately shown nonzero at the chosen point.

## Audit

`research/T15/axioms_u3.lean` prints exactly
`[propext, Classical.choice, Quot.sound]` for the four generic lattice lemmas
and all six canonical field theorems.
