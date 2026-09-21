# Lane 221 — force-path attempts

## Successful route

Continued the uncommitted ForcePath/axiom-audit drafts after the capacity cutoff.
The initial module build succeeded; its existing proofs were retained.

`MemForceR` already supplies a continuous order-two datum path with global
`MemLp` bounds. Lane 219's `orderTwoToHalf` transports continuity and `MemLp`;
homogeneous uniqueness identifies its image with the chosen `criticalForceHalf`
on future times (almost everywhere for the restricted positive-time measure).
Thus no reconstruction from C01 jets is necessary. An order-one identification
lemma is also exported. The module introduction was corrected to say order two.

For G2, transport every admissible half-order inhomogeneous path through the
Bessel-to-homogeneous CLM. Its vector contraction follows by summing squared
component bounds in `PiLp 2`. Compare eLpNorms before taking the path infima.
G3 follows from this comparison and lane 165's finite inhomogeneous norm; the
canonical homogeneous path's membership/measurability is proved separately.

For the prefix bound, every homogeneous path has norm `criticalForceAt` on
future slices. Rewrite the nonnegative integral as a lintegral, enlarge
`Ioc 0 S` to `Ioi 0`, and take the infimum. Continuity gives integrability and
FTC. Nonnegativity gives monotonicity of prefix integrals.

The scalar bootstrap expects a globally continuous y; the classical solution
only supplies continuity inside its lifespan. Compose y with `projIcc 0 S`,
then transfer the local energy derivative by eventual equality on `Ioo 0 S`.
This closes the promoted theorem with no additional analytic assumption.

## Failed elaboration and repair

The nonzero compact bump witness in the inherited conformance draft failed:

```
invalid `▸` notation, expected result type of cast is F p = 0
```

The scalar equality was hidden by the local definition `F`. An explicit
`change (tb p.1 * xb p.2) • ... = 0` followed by `rw [hz, zero_smul]`
fixes the proof. The witness is a smooth space-time bump supported at positive
times, nonzero at `(2, 0)`, and belongs to `MemForceR` by the established compact
force constructor. Both zero and nonzero conformance examples now compile.

## Scope and validation

G2/G3/G4 and the zero-datum S2 wiring close. The estimate holds on `[0,S]`
for `0 ≤ S < T`, since the solution is defined on `[0,T)`. General initial data,
maximal-endpoint gluing, continuation and registration are separate work.
No fallback hypothesis, proof admission, or heartbeat override was introduced.
See REPORT_221.md for gate results.
