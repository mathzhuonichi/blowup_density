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

## Verification

The direct theorem module, literal-target probe, and exact axiom check compile.
The registration and full repository gates are recorded in `REPORT_511.md`.
