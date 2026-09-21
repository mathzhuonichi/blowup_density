# T20 reconciled comparison

| Paper clause | Lean field | Provenance/ruling |
|---|---|---|
| prop:critical, eq:smallcritical | `globalRegularity` | B shape, A naming; zero datum and one fixed `c` |
| mean reduction | `reductionRegular`, `meanBound`, `meanFreeEquation` | B factoring, A residual and real-integral spellings |
| :411 | `constantTransportSkew`, `constantTransportCommutesLambda` | restored from B; integrability premises dropped |
| eq:criticalenergy / eq:bintegral / eq:ybound | `criticalEnergy`, `bIntegral`, `yBound` | exact quantifier order reconciled |
| eq:H1energy | `hOneEnergy` | A square spelling, B solution shape |
| :492-500 | `continuationBound` | retained from B |

## Proof dependencies

See `RECONCILIATION.md` §4: torus measurability and MemLp, zero datum and T11 mean identities, mean-free decomposition, residual identity, mean-force contraction, transport skew/Λ commutation, fractional Sobolev bridges, critical and H1 energy estimates, scalar bootstrap, orthogonal H2 continuation, and T11 maximality/continuation.

## Open questions for the owner

None specific to T20. The inherited T11 restart H¹-vs-H³ narrowing is tracked
in `research/T11/H1_GAP.md`; the canonical consumer result is recorded below.

## Canonical module status (lane 381)

`NSFormalization.Section3.T20.CriticalRegularity` now restates the reconciled
T20 namespace over canonical Section3/T10, T11, and T12 vocabulary: 17 helper
definitions, a 23-field `CriticalRegularityTAPI`, and the existential statement
definition. `research/T20/probes/api_on_canonical.lean` checks all helper
definitions and the statement seam and supplies both fieldwise structure
conversions with `rfl` round trips.

The H¹ review is closed in `research/T20/H1_CHECK.md`: the only two order-one
occurrences are in the copied T11 manuscript continuation structure, not the
T20 API. The current T20 consumer route needs only the ball-free criterion
fields, so the canonical H³ continuation implementation suffices without
assuming `PeriodicRestartH1`.
