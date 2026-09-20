# T19 U15 attempts — assembly and registration

## Successful route

- Assembled the canonical `PeriodicDensityAPI`, `MixedRegionAPI`,
  `StrongClosureAPI`, and `ProjectionAPI` directly from the thirteen U1--U14
  theorems.  The four headline statement proofs are record projections; the
  projection statement is the conjunction of its first two record fields.
- Restated the 3/3/4/3 `Prop` records over registered T10/T11/T15 vocabulary.
  The mixed norm reuses `Contracts.V1.Scaling3.mixedLebesgueENormT`; the mixed
  exponent uses the reconciliation-approved registered
  `Contracts.V1.alpha`.  Both are definitionally equal to the canonical T15
  spellings.
- Moved every `ClassicalSolutionT` witness through
  `Bindings.TorusLocalTheory.toContract`/`ofContract`.  Rewrote every lifespan
  occurrence through `maximalLifespanT_eq`, including the extended breakdown
  set and all nested family witnesses.  This is the only non-`rfl` vocabulary
  transport.
- Kept the T18 record out of the contract as decided in reconciliation.  The
  canonical proof uses U0's insertion constructor, whose reference is
  zero-extended only to discharge T17's global slab inputs (route G5); the
  original velocity is recovered on `[0,T)` before any T19 conclusion.
- Proved non-vacuity by applying the registered periodic density statement to
  the actual zero initial datum and zero force at `ν = 1`, `T = 1`, `s = 0`,
  radius `1`, then selecting the resulting force and recording both its
  breakdown-set membership and strict distance bound.

## Resolved development errors

- The first contract draft used the visually similar calligraphic character
  `𝒩` instead of Lean's neighbourhood notation `𝓝`; replacing it by the exact
  canonical token fixed parsing of `𝓝[>] 0`.
- The first drift guard qualified `criticalOrder` at
  `Contracts.V1.criticalOrder`; its registered namespace is
  `Contracts.V1.Data.criticalOrder`.
- `Contracts/V1/Density.lean` was initially considered for a `T` suffix, but
  no unsuffixed Density contract exists.  The new torus registration therefore
  uses the requested unsuffixed module name without changing any existing V1
  file.

No named input, placeholder proposition, admission, or unproved analytic
claim remains.  The contract deliberately omits an initial-data topology,
optimality, T20 critical regularity, and the separate peaks remark, exactly as
ruled in `RECONCILIATION.md`.
