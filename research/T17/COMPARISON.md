# T17 reconciled comparison (`lem:correction`)

Paper source: `paper/sections/03-torus.tex:218-285`.  The binding decisions are
`research/T17/RECONCILIATION.md:§2-§3`; provenance is retained below.

## Draft A paper-clause table (provenance)

| Paper clause | Draft A | Section 4 counterpart |
|---|---|---|
| `eq:H`, lines 219–223 | `correctionForce` | `I02.correction`: `CorrectionAPI.force_formula` |
| smooth across `T`, zero outside cutoff, line 225 | `force_smooth`, `force_support` | `force_smooth`, `force_compactSupport`, `force_support` |
| spatial support volume `O(ε³)`, line 225 | `spatialVolumeConst`, `force_spatial_volume` | same fields |
| temporal support length `O(ε²)`, line 225 | `force_time_length` | same field |
| first `eq:derivativebounds`, lines 226–228 | `correctionDerivConst`, `correction_derivative_bound` | same fields |
| second `eq:derivativebounds`, lines 229–230 | `forceDerivConst`, `force_derivative_bound` | same fields |
| `eq:wE`, lines 233–234 | `energyConst`, `correction_energy_bound` | whole-space `Data.energyENorm` counterpart |
| `eq:Hmixed`, lines 235–237 | `mixedConst`, `force_mixed_bound`, `correctionForceExponent`, `force_exponent_identity` | registered `Contracts.V1.alpha` |
| `eq:HHs`, lines 238–240 | `sobolevConst`, `force_sobolev_path`, `force_sobolev_bound` | explicitly outside V1 correction |
| constants independent of ε, line 242 | record data before ε; `eps_le_one` | same house style |
| fixed-cylinder argument, lines 245–273 | profiles and `UniformProfileHypotheses` | binding infrastructure |

### Draft A choices and ambiguities

A used a Type-valued API, real profile constants, the closed cylinder, a concrete
cutoff–curl profile, a torus-path mixed norm, and explicit `MemLp`/datum guards.
Its ambiguities were the torus support projection convention, operator-norm
uniform smoothness, the profile-only rescaling scope, exponent equality versus
norm inequality, and endpoint localization.

### Draft A needs-a-lemma list

1. Rescale T16’s correction formula and identify the correction profile.
2. Apply the affine chain rule with ε, ε², and ε⁻² factors.
3. Obtain uniform derivative bounds from joint smoothness on the compact cylinder.
4. Transfer central support to `periodicSet`, prove periodicity, and compute Haar support volume/time length.
5. Establish periodic energy scaling and honest `L²` slices.
6. Prove mixed-norm change of variables, including both ∞ endpoints and measurable `Lp` paths.
7. Apply T13 localization and endpoint identities and assemble the Sobolev datum path.

### Draft A implementation candidates

`Paper1/CorrectionProfile.lean`: `profile_smooth`, `profile_uniform_derivative_bound`,
`profile_support`, `physicalCorrection_rescale`, `physical_mixed_derivative_bound`.
`Paper1/CorrectionForceProfile.lean`: `forceProfile_eq_operators`,
`physicalForce_eq_profile`, `forceProfile_uniform_derivative_bound`,
`physicalForce_spatial_derivative_bound`.
`Paper1/CorrectionEnergy.lean`: `compact_energy_bound`,
`physicalCorrection_uniform_energy`, `physicalCorrection_total_direction_energy`.
`Paper1/CorrectionMixedNorms.lean`: `physical_force_mixed_bound`,
`physical_force_spatial_memLp`, `physical_force_mixed_memLp`.
`Paper1/CorrectionPositiveNorms.lean`, `CorrectionVectorNorms.lean`, and
`Paper1/PeriodicCorrectionEndpointRates.lean` (`correction_vector_whole_endpoint_rates`).

## Draft B paper-clause table (provenance)

| Paper clause | Draft B declaration/field | Registered `I02.*` counterpart |
|---|---|---|
| `eq:H`, lines 219–223 | `correctionForce` | V1 `force_formula` |
| smooth zero extension, line 225 | `force_smooth`, `force_periodic` | V1 smoothness; periodicity added |
| spatial volume `O(ε³)`, line 225 | `force_support`, `force_spatial_volume` | same names |
| temporal length `O(ε²)`, line 225 | `force_support`, `force_time_length` | same names |
| first `eq:derivativebounds`, lines 225–228 | `correction_derivative_bound` | same name |
| second `eq:derivativebounds`, lines 229–230 | `force_derivative_bound` | same name |
| `eq:wE`, lines 232–234 | slice guards and `correction_energy_bound` | T10 torus energy |
| `eq:Hmixed`, lines 235–237 | `correctionAlpha`, mixed norm, slice guard, `force_mixed_bound` | V1 `alpha` |
| `eq:HHs`, lines 238–240 | `sobolevConst_finite`, `force_sobolev_bound` | outside V1 |
| constants uniform for small ε, line 242 | `D.ε₀`, `eps_le_one`, constant data | V1 threshold/constants |
| fixed-cylinder argument, lines 245–273 | concrete profiles and identities | implementation infrastructure |
| localization transfer, line 284 | T13 `LocalizationAPI` parameter | outside V1 |

### Draft B choices and ambiguities

B used inline Type-valued fields, the literal `[-2,2] × closedBall`, concrete
reference/potential/correction/force profiles, a torus `Lp` path norm, finite
`ENNReal` constants, and no packet parameter.  Its ambiguities were whether the
mixed norm belongs in T10, whether spatial support means a projection, and how
to insert the general T16 ball into T13’s fixed chart.

### Draft B needs-a-lemma list

- Derive both profile identities by parabolic differentiation.
- Turn joint profile smoothness into all uniform constants and physical derivative bounds.
- Derive torus support volume/duration and `MemLp`/measurable-path witnesses.
- Prove periodic mixed-norm scaling, both ∞ endpoints, and exponent arithmetic.
- Adapt force slices to `periodize`, apply localization/endpoints, and integrate the rates.

### Draft B implementation candidates

`CorrectionProfile`: `profile_smooth`, `profile_support`,
`profile_uniform_global_derivative_bound`, `physicalCorrection_rescale`,
`physicalCorrection_eq_profile`, `physical_mixed_derivative_bound`.
`CorrectionForceProfile`: `forceProfile`, `forceProfile_smooth`, `forceProfile_support`,
`physicalForce_eq_profile`, `forceProfile_uniform_derivative_bound`,
`physicalForce_spatial_derivative_bound`.
`CorrectionEnergy`: `physicalCorrection_uniform_energy`,
`physicalCorrection_total_direction_energy`.
`CorrectionMixedNorms`: `physical_force_spatial_memLp`,
`physical_force_mixed_bound`, `physical_force_mixed_memLp`.
`CorrectionPositiveNorms`, `CorrectionVectorNorms`, and
`PeriodicCorrectionEndpointRates` provide the positive-order and endpoint inputs.

## Reconciled paper clause → Lean field table

| Paper clause | Reconciled field(s) | A/B provenance and ruling |
|---|---|---|
| `eq:H` `:219-223` | `correctionForce` | A=B; registered operator order retained |
| fixed-cylinder profiles `:245-273` | `fixedProfileCylinder`, profile fields, `correction_profile_identity`, `force_profile_identity` | B inline fields + A concrete potential; both identities kept |
| smooth/periodic/support `:225` | `force_smooth`, `force_periodic`, `force_support` | B periodicity; A open-ball support |
| support volumes `:225` | `torusSpatialSupport`, `torusTemporalSupport`, `force_spatial_volume`, `force_time_length` | B torus-lift projections |
| derivative bounds `:226-232` | `correction_derivative_bound`, `force_derivative_bound` | A=B; unit directions and ε powers retained |
| `eq:wE` `:234` | slice `MemLp` guards, `energyConst`, `correction_energy_bound` | both guards; A real constant + one `ENNReal.ofReal` |
| `eq:Hmixed` `:235-238` | `force_spatial_memLp`, `mixedConst`, `force_mixed_bound` | T15 quantifiers `[Fact (1≤p)], 1≤q`; registered `alpha`; no exponent field |
| `eq:HHs` `:239-242` | `sobolevConst`, `sobolevConst_pos`, `forceSobolev_memLp`, `force_sobolev_bound` | A witness guard respelled as T15 `MemForceSobolevT` |
| geometry / chart | `place : PlacementData P`, `ball_in_chart`, `eps_le_placement` | A geometry repackaged through T15; B lacked it |
| T16/T13 inputs | `potential`, `localization` | both drafts had parameters; reconciliation makes them fields |
| completed existential form | `correctionStatement` | added shape-only closure with pinned data |

## Proof dependencies

1. Rescale T16’s `correction_formula` on the chart and identify it with `W_ε`; identify `ε⁻¹•D.potential(chart)` with the displayed potential integral.
2. Apply the affine chain rule to `force_profile_identity` with exact ε, ε², ε⁻² factors.
3. Obtain uniform derivative constants from joint smoothness of `(ε,z)` on `[0,ε₀] ×` the fixed cylinder, including the `eps_space`/`eps_time` chart containment for the dropped `V_ε`/`𝒜_ε` step.
4. Transfer one central copy to `periodicSet`, prove periodicity of `correctionForce`, and compute torus support volume/duration.
5. Prove periodic energy scaling and honest `L²` slice paths for `energyENormT`.
6. Prove mixed-norm change of variables for all `1≤p,q≤∞`, including both ∞ endpoints and normalized-Haar/`|Q|=1` identification.
7. Express each force slice as `periodize` of its compact central copy; apply `LocalizationAPI.localization`, `endpoint_zero`, and `endpoint_one`, integrate in time, and assemble the T10 Sobolev datum path for `forceSobolev_memLp`.
8. Use `ball_in_chart` plus `place.chartBall_in_cube` for T13’s chart hypothesis; `x₀+εK_*⊆B` is already `place.eps_space`.

The reconciliation also records two implementation files sitting on item 7:
`Paper1/CorrectionForceNorms.lean:78,100`
(`scalarProfile_uniform_homogeneous(_time)`) and
`Paper1/PeriodicCorrectionEndpointInstantiation.lean:30`
(`eventually_correction_coordinate_periodized_endpoint_product`).

## Open questions for the owner

- Should `CorrectionAPI` carry `place : PlacementData P`? The reconciled spec does so for definitional sharing of `T,x₀,K_*,B,ε₀`, at the cost of a packet parameter unused by the correction mathematics.
- Should `mixedLebesgueENormT` move into the T10 data contract? The spec keeps the T17-local copied vocabulary; registration is deferred to T18.
