# B5 T³ attempts (lane 511)

The periodic endpoint proof follows the exact consumer check recorded by lane
508.  `Section3/T11/RestartBeyond.lean:restartBeyond` consumes its named local
input only through the call to `restart H`.  The new canonical theorem copies
that proof body and replaces only that supplier with the unconditional
`h1RestartT` theorem.

## Closed proof route

- Apply `h1RestartT` at the endpoint `S` and retain its returned duration `d`.
- Choose the existing interior basepoint `t₀ = max 0 (S - d/2)`, so the restart
  interval reaches strictly past `S`.
- Restart from the actual velocity slice, glue on the overlap, and use the
  existing velocity and normalized-pressure uniqueness theorems against each
  shorter `SolvesBelowT` witness.
- Return `δ = t₀ + d - S`; no additional shrinking is needed.

The theorem has the literal `h1UniformEndpointT` target shape.  It introduces
no named input, force-shift class assertion, admission, custom axiom, or
heartbeat override.

## Registration adapters

`Contracts/V2/TorusLocalTheory.lean` reuses all V1 definitions and structures,
adding only the two H¹ fields.  The binding uses the existing `toContract`,
`periodicLocalRegularity_toContract`, and `solvesBelowT_eq` conversions.  Its
zero-solution probe selects the finite radius
`periodicSobolevENorm 1 (0 : SpatialField)` and instantiates the registered
`restartBeyond` field on genuine classical zero solutions at every shorter
horizon.

The first direct contract check omitted the open namespace containing the
reused norm and reported:

```text
Function expected at periodicSobolevENorm
Hint: The identifier `periodicSobolevENorm` is unknown
```

Opening `Contracts.V1.TorusData` fixes the vocabulary import without restating
the norm.

## Verification

The direct theorem module, literal-target probe, and exact axiom check compile.
The registration and full repository gates are recorded in `REPORT_511.md`.
