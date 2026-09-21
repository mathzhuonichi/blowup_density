# T17 draft A comparison

## Paper clauses and Lean fields

| Paper clause | Draft A | Section 4 counterpart |
|---|---|---|
| `eq:H`, lines 219–223 | `correctionForce` | `I02.correction`: `CorrectionAPI.force_formula` |
| smooth across `T`, zero outside the cutoff, line 225 | `force_smooth`, `force_support` | `force_smooth`, `force_compactSupport`, `force_support` |
| spatial support volume `O(epsilon^3)`, line 225 | `spatialVolumeConst`, `force_spatial_volume` (normalized Haar measure on `T^3`) | `spatialVolumeConst`, `force_spatial_volume` |
| temporal support length `O(epsilon^2)`, line 225 | `force_time_length` | `force_time_length` |
| first half of `eq:derivativebounds`, lines 226–228 | `correctionDerivConst`, `correction_derivative_bound` | same field names |
| second half of `eq:derivativebounds`, lines 229–230 | `forceDerivConst`, `force_derivative_bound` | same field names |
| `eq:wE`, lines 233–234 | `energyConst`, `correction_energy_bound` using T10 `energyENormT` | `energyConst`, `correction_energy_bound` using the whole-space `Data.energyENorm` |
| `eq:Hmixed`, lines 235–237 | `mixedConst`, `force_mixed_bound`; `correctionForceExponent` is explicit and `force_exponent_identity` records `-2+3/p+2/q = alpha(p,q)+1` | `mixedConst`, `force_mixed_bound`, with `Contracts.V1.alpha` |
| `eq:HHs`, lines 238–240 | `sobolevConst`, `force_sobolev_path`, `force_sobolev_bound` using T10 `forceSobolevENormT` and a T13 `LocalizationAPI` parameter | none: `Contracts.V1.Correction` explicitly leaves the fractional bound to I03 |
| constants independent of small `epsilon`, line 242 | constants are record data outside every `epsilon` quantifier; `eps_le_one` normalizes the common range | the same record-data pattern and `eps_le_one` |
| fixed-cylinder argument, lines 245–273 | `fixedProfileCylinder`, the three rescaled profiles, `rescaledForceBracket`, and `UniformProfileHypotheses` | not exposed by `I02.correction`; it is internal to the binding implementation |

## Choices

- `CorrectionAPI` is `Type`-valued. Constants are selected before the scale, matching A03/A05/I02 and making uniformity visible to downstream consumers.
- The fixed cylinder is the literal closed set `tsupport D.η × tsupport D.θ`. T16 makes both factors compact and places them inside `(-2,2)` and a fixed spatial ball.
- `rescaledCorrectionProfile` is the single-chart cutoff–curl formula from lines 256–259. It is not a rescaling of the globally periodic correction, which would contain infinitely many Euclidean lattice copies.
- The reference, potential, correction, and bracket profiles are concrete definitions tied to `v` and `D`; T15 packet declarations are neither imported nor assumed.
- The mixed norm is an infimum over strongly measurable paths in the actual periodic `Lp` space. The Sobolev norm is T10's fail-safe Fourier-datum norm. Explicit `MemLp`/datum-path fields rule out junk-value readings.
- The paper's range `1 <= p,q <= infinity` is represented by `p q : ENNReal` with `Fact (1 <= p)` and `Fact (1 <= q)`; the upper bounds are automatic. `toReal infinity = 0` gives the intended endpoint reciprocal.

## Ambiguities resolved or retained

- A periodic physical lift cannot have compact Euclidean spatial support. Consequently, the `O(epsilon^3)` clause measures `tsupport` after `torusLift` with normalized Haar measure, while `force_support` records all Euclidean lattice copies through `periodicSet`.
- “Uniformly smooth on a fixed cylinder” is rendered as a bound on the operator norm of every `iteratedFDeriv` order. This is slightly stronger than separately listing coordinate derivatives and directly implies every displayed multi-index estimate.
- The displayed force rescaling is asserted only on the fixed cylinder. Globally rescaling a periodized field would encounter other lattice copies; global physical estimates instead use periodicity plus the single-copy chart hypothesis.
- `eq:Hmixed` contains an equality of exponents, not an equality of norms. Draft A records the norm inequality with the first explicit exponent and a separate exact identity with `alpha+1`.
- At `s=0,1`, `eq:HHs` is read through T13's endpoint clauses; for `0<s<1`, it is read through `LocalizationAPI.localization`. One constant `C_s` controls the complete inhomogeneous sum.

## Needs a lemma

1. Rescale T16's `correction_formula` on the coordinate chart and identify it with `rescaledCorrectionProfile`.
2. Apply the affine chain rule to prove `UniformProfileHypotheses.force_rescaling`, with the exact `epsilon`, `epsilon^2`, and `epsilon^-2` factors.
3. Derive uniform derivative bounds for the reference, potential, correction, and force bracket from joint smoothness on `[0,epsilon0] × fixedProfileCylinder D`.
4. Transfer central-copy support to `periodicSet`, prove periodicity of `correctionForce`, and compute its Haar support volume and time length.
5. Establish the periodic energy scaling and construct the honest `L2` slice paths used by `energyENormT`.
6. Prove the periodic mixed-norm change of variables, including `p=infinity` and `q=infinity`, and construct the strongly measurable `Lp` path.
7. Express each force slice as the periodization of its compactly supported central copy, apply T13 localization (plus both endpoint identities), and assemble the strongly measurable T10 Sobolev datum path for `eq:HHs`.

## Existing implementation candidates

- `Paper1/CorrectionProfile.lean`: `profile_smooth`, `profile_uniform_derivative_bound`, `profile_support`, `physicalCorrection_rescale`, `physical_mixed_derivative_bound`.
- `Paper1/CorrectionForceProfile.lean`: `forceProfile_eq_operators`, `physicalForce_eq_profile`, `forceProfile_uniform_derivative_bound`, `physicalForce_spatial_derivative_bound`.
- `Paper1/CorrectionEnergy.lean`: `compact_energy_bound`, `physicalCorrection_uniform_energy`, `physicalCorrection_total_direction_energy`.
- `Paper1/CorrectionMixedNorms.lean`: `physical_force_mixed_bound`, `physical_force_spatial_memLp`, `physical_force_mixed_memLp`.
- `Paper1/CorrectionPositiveNorms.lean` and `CorrectionVectorNorms.lean`: positive-order profile bounds and vector assembly.
- `Paper1/PeriodicCorrectionEndpointRates.lean`: `correction_vector_whole_endpoint_rates` supplies the whole-space `s=0,1` rates, but still needs the T13 single-copy periodization adapter.
