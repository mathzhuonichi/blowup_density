# Lane 258: R47 assembly

## Result

`Bindings/GridAssembly.lean` proves `rGrid_choose_of_realization`, with the exact
`RGridAPI.choose` statement and only `CompactHomogeneousRealization` as an
additional input. `rGridFamily_of_data` constructs the full record. The two
specification structures are copied byte-for-byte (including field docstrings)
from `research/R47/Spec.lean`; their original namespace is retained. They are
not weakened or replaced by a local approximation predicate.

## Construction and successful routes

1. `exists_ball_in_common_cell` chooses a single positive-radius ball after the
   entire grid family has been supplied, including the empty family.
2. Lane 233's public constructor fixes `(x₀,r)=(0,1)`. Reuse its packet constructor
   `insertionFromData_packet`, then apply `correction` with the chosen ball and
   the actual supplied reference. Apply `scaling C thresholds` and
   `insertionFamily`. All reference data and ball coordinates agree by reduction;
   no reference uniqueness transport is needed. `Bindings.Packet` is not imported.
3. Use `InsertionLifespan.sol_fullHorizon`, `memForceR_force`, and `lifespan_eq`
   on that same family. This avoids unnecessarily constructing the V2 wrapper,
   whose `regular` field asks for a reference beyond the correction margin.
4. The spec demands classical solutions at every real scale, while R42 exports
   them only at admissible scales. Extend both force and solution families by
   replacing inadmissible scales with `A.ε₀`. Admissible scales are unchanged;
   `Ioc_mem_nhdsGT A.eps_pos` transports all limits to the extension.
5. History, compactness and all supports are projections of that record.
   `velocity_gridObservation_eq` and `force_gridObservation_eq'` apply with
   each containing cell; the latter receives the original `MemForceR g`.
   The pressure gauge is the single function `fun _ => 0`, since the reference
   is used directly, with its original pressure.
6. Energy convergence uses lane 249's `mainThresholds_energyConvergence`.
   The inhomogeneous negative-order force term uses `A.forceConvergence` at
   `(q,s)=(2,-1)`.
7. The literal mixed norm is handled directly, without an order-zero isometry
   bridge: the correction's registered `force_mixed_bound` has exponent `3/2`,
   and the packet's existing mixed-norm convergence has exponent `1/2`.
   `grid_mixed_add` constructs the sum of the two measurable `Lp` slice paths
   and applies the Bochner triangle inequality. Thus the unresolved general
   equality `mixedLebesgueENorm 1 2 = forceSobolevENorm 1 0` is not an input.
8. `grid_homogeneous_add` uses compact homogeneous paths, the existing
   integrability-carrying subtraction theorem, and datum uniqueness to prove
   additivity. The physical Schwartz pairings are integrable by compactness
   and smoothness; no totalized-integral linearity is assumed. Lane 250's
   correction/packet bounds give exponents `3/2` and `1/2`, respectively.
   `CompactHomogeneousRealization` is used only in this homogeneous chain.

## Rejected routes and Lean corrections

- Do not use lane 233's fixed ball for arbitrary prescribed grids.
- Do not assert that the two order-zero norm spellings are definitionally equal.
  The direct mixed-norm proof makes that bridge unnecessary for this theorem.
- Do not choose an R42 solution outside its admissible scale interval. Totalize
  the family as above; the spec explicitly permits arbitrary extensions there.
- Eliminating `∃ x₀ r, ...` directly inside a data-valued `def` failed with
  `Exists.casesOn can only eliminate into Prop`. First apply `Classical.choice`
  and construct the nonempty witness in Prop.
- `simpa [alpha]` left rational exponents unnormalized. Use `norm_num` on the
  supplied inequality before applying it. A `convert` attempt also exposed an
  irrelevant ENNReal order-instance equality; it is unnecessary in the final proof.
- Lambda-expanded fields sometimes prevent `rw` from matching. Use an explicit
  `change` for the parabolic force and an explicit equality for `A.g = g`.

## Validation

All seven implementation declarations print exactly
`[propext, Classical.choice, Quot.sound]`. The audit contains concrete
`ν=T=δ=1`, `a=g=0` examples for `n=0` and `n=1` (one complete unit Cartesian
grid), conditional only on the same realization input. No heartbeat override
is used. Direct checking of `Bindings/GridAssembly.lean` has zero output.
See `REPORT_258.md` for gate results and the remaining supplier boundary.
