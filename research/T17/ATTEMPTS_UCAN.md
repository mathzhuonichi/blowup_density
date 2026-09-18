# T17 U-CAN — canonical correction mapping

Lane 394 is a statement-restatement unit.  It introduces no inhabitant of the
record and proves no analytic field.  The source is
`research/T17/Spec.lean:679-985`; the target is
`NSFormalization.Section3.T17.Correction` over T15's raw-field placement.

## Parameter and vocabulary mapping

| Spec token | Canonical token | Reason |
|---|---|---|
| `{P : PacketAPI ν}` | raw `u p f K` parameters | T15 U-CAN removes the contract packet structure from `formalization/` |
| `place : PlacementData P` | `place : T15.PlacementData u p f K` | lane 384's 17-field structure |
| `P.velocity` | `u` | the only packet projection used by correction mathematics |
| `place.x₀`, `place.T` | unchanged projections | G3 bare-`(x₀,T)` canonical profile theorems are instantiated by these projections |
| Spec `CutoffData`, `LocalPotentialAPI` | canonical T16 records | structure-exception adapters are fieldwise in the probe |
| Spec `LocalizationAPI` | canonical T13 record | six-field adapter in the probe |
| registered `alpha p q` | canonical `T15.alphaT p q` | definitionally equal (`rfl`), without a `Contracts.*` import |
| Spec profile helpers | canonical bare `(x₀,T)` helpers | U3 and U4 spelling; the probe supplies all `rfl` bridges |

The base did not contain lane 375's `ForceProfile.lean`, so its landed source
was restated as a new canonical file.  `CorrectionProfile.lean`,
`Transport.lean`, `CorrectionDeriv.lean`, and `ForceDeriv.lean` were already on
the base and are imported unchanged.

## Field mapping (all 45 fields, in source order)

| # | Spec field | Canonical field/type substitution | Proof unit / status |
|---:|---|---|---|
| 1 | `potential` | `LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D` | T16 record adapter |
| 2 | `localization` | canonical `T13.LocalizationAPI` | T13 record adapter |
| 3 | `viscosity_pos` | unchanged | assembly datum |
| 4 | `radius_pos` | unchanged | assembly datum |
| 5 | `ball_in_chart` | raw placement projections | assembly datum |
| 6 | `eps_le_placement` | raw placement projections | assembly datum |
| 7 | `reference_periodic` | canonical `T10.IsPeriodicOn` | assembly datum |
| 8 | `correction_profile_smooth` | `place` replaced by `place.x₀ place.T` | U3, exact in probe under `hv` |
| 9 | `correction_profile_support` | same | U3, exact in probe under `hv` |
| 10 | `correctionProfileConst` | unchanged data field | U3 choice |
| 11 | `correctionProfileConst_nonneg` | unchanged | U3, exact in probe |
| 12 | `correction_profile_uniform` | bare profile helper | U3, exact under `hv`, `D.ε₀≤1` |
| 13 | `force_profile_smooth` | bare force-profile helper | U4, exact in probe under `hv` |
| 14 | `force_profile_support` | same | U4, exact in probe under `hv` |
| 15 | `forceProfileConst` | unchanged data field | U4 choice |
| 16 | `forceProfileConst_nonneg` | unchanged | U4, exact in probe |
| 17 | `force_profile_uniform` | bare force-profile helper | U4, exact under `hv`, `D.ε₀≤1` |
| 18 | `correction_profile_identity` | bare chart/profile helpers | U3, exact under `hv` and `potential` |
| 19 | `force_profile_identity` | bare chart/profile helpers | U4 chart-force theorem; U2/assembly still supplies the lattice-to-chart germ bridge | **Update (fix after review 394): CLOSED** — `force_profile_identity_canonical` in `research/T17/probes/force_profile_canonical.lean` proves the literal canonical field type (via `Transport.force_eq`, the `latticeLift_eq_of_ball` single-copy germ and `physicalForce_eq_rescaledForceProfile`); the only extra premise is the documented G1 `hv`.
| 20 | `force_smooth` | canonical `T17.correctionForce` | later T17 unit |
| 21 | `force_periodic` | same | U2 supplies periodicity |
| 22 | `force_support` | canonical `T16.periodicSet`, raw placement | later T17 unit |
| 23 | `spatialVolumeConst` | unchanged data field | later T17 unit |
| 24 | `spatialVolumeConst_nonneg` | unchanged | later T17 unit |
| 25 | `force_spatial_volume` | canonical torus support projection | later T17 unit |
| 26 | `force_time_length` | canonical torus support projection | later T17 unit |
| 27 | `correctionDerivConst` | unchanged data field | U5 choice |
| 28 | `correctionDerivConst_nonneg` | unchanged | U5 |
| 29 | `correction_derivative_bound` | canonical T16 correction | U5, exact in probe under `hv`, `ε₀≤1` |
| 30 | `forceDerivConst` | unchanged data field | U6 choice |
| 31 | `forceDerivConst_nonneg` | unchanged | U6 |
| 32 | `force_derivative_bound` | canonical correction force | U6, exact in probe under `hv`, periodicity, `ε₀≤1` |
| 33 | `correction_slice_memLp` | canonical torus lift/measure | later T17 energy unit |
| 34 | `correction_gradient_memLp` | canonical spatial gradient | later T17 energy unit |
| 35 | `energyConst` | unchanged data field | later T17 energy unit |
| 36 | `energyConst_nonneg` | unchanged | later T17 energy unit |
| 37 | `correction_energy_bound` | canonical T10 `energyENormT` and `place.T` | later T17 energy unit |
| 38 | `force_spatial_memLp` | canonical torus lift/measure | later T17 mixed unit |
| 39 | `mixedConst` | unchanged data field | later T17 mixed unit |
| 40 | `mixedConst_nonneg` | unchanged | later T17 mixed unit |
| 41 | `force_mixed_bound` | `T15.mixedLebesgueENormT`, `T15.alphaT` | later T17 mixed unit |
| 42 | `sobolevConst` | unchanged data field | later T17 Sobolev unit |
| 43 | `sobolevConst_pos` | unchanged | later T17 Sobolev unit |
| 44 | `forceSobolev_memLp` | `T15.MemForceSobolevT` | later T17 Sobolev unit |
| 45 | `force_sobolev_bound` | canonical T10 `forceSobolevENormT` | later T17 Sobolev unit |

## Probe conversions

`correction_canonical.lean` contains the literal reconciled Spec block under a
new namespace, then gives:

- `placementOfSpec` / `placementToSpec` through the lane-384 raw placement;
- `cutoffOfSpec` / `cutoffToSpec`;
- `localPotentialOfSpec` / `localPotentialToSpec` (all 26 Prop fields);
- `localizationOfSpec` / `localizationToSpec` (all six Prop fields);
- `ofSpec` / `toSpec` naming all 45 correction fields, with both round trips;
- ten definitional vocabulary bridges, all proved by `rfl`;
- `exact` checks for the landed U3 profile fields, U4 force-profile fields in
  their landed chart-force scope, and U5/U6 derivative bounds.

## G1 and the honest U4 residual

Per the lead decision, `CorrectionAPI` has no `reference_smooth` field.  U3,
U4, U5, and U6 retain their proved `hv : ContDiff ℝ ∞ v` hypotheses.  The final
assembly must obtain `hv` by chart truncation or state it as an assembly
hypothesis.

The landed U4 identity is the single-copy chart-force identity.  It does not
by itself prove the record's periodized `force_profile_identity`; U2's present
`Transport.force_eq` plus the local single-copy germ is the required bridge.
That bridge is now closed at the concrete `correctionData` by
`NSFormalization.Section3.T17.force_profile_identity_canonical` in
`research/T17/probes/force_profile_canonical.lean`.  The proof obtains
`r < 1/2` from the record's `radius_pos`, `ball_in_chart`, and
`place.chartBall_in_cube`, collapses the lifted single-copy force on each
profile-cylinder chart point with `T16.latticeLift_eq_of_ball`, and then applies
`physicalForce_eq_rescaledForceProfile`.  No premise beyond the record's own
preceding hypotheses and the documented G1 hypothesis `hv` is used.
