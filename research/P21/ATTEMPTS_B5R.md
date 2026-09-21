# B5 R³ attempts

## Closed route

1. Apply lane 507's `h1RestartAt` with `hS.le`.  Its one positive duration is
   already chosen before the solution and every restart time in `[0,S)`.
2. Pass that per-time inequality directly to
   `A04.restartBeyond_of_restartAt`.  This proves the reusable non-strict
   theorem `restartBeyondH1_le` with the full duration.
3. Return half that duration.  Since `S > 0` and `δ > 0`,
   `ofReal (S + δ/2) < ofReal (S + δ)`; transitivity with the non-strict
   theorem gives the exact strict target `restartBeyondH1`.
4. At the registered boundary, convert the local restart solution with
   `maximalPartial_ofA02`, transport its four regularity fields with
   `localTheoryV2_regularity_ofA02`, transport `SolvesBelow` with
   `continuationV2_solvesBelow_iff`, and rewrite maximal lifespan with
   `maximalPartial_maximalLifespanR_eq`.

## Resolved elaboration findings

- `H1Restart.lean` already imports the endpoint bookkeeping through its shifted
  extension dependency, so the new proof module needs only that one direct
  import.
- Direct `lake env lean Tests/ContinuationV3.lean` initially lacked the newly
  created contract object file; building `Tests.ContinuationV3` installed the
  dependency closure, after which all three new registered modules checked
  directly.
- In the zero-solution probe, the contract's zero spacetime slice elaborated as
  the zero function rather than a displayed lambda.  An explicit `change` to
  the implementation Sobolev norm and `erw` across the definitionally equal
  zero functions discharged the norm bound.
- V2 exposes a parameterized `ContinuationV2API`, but no standalone statement
  alias.  Therefore V3 registers its two-field API alone; the unchanged V2
  registration continues to cover all five earlier fields.

No residual Lean goal, new analytic hypothesis, or blueprint-status change
remains in the whole-space B5 unit.
