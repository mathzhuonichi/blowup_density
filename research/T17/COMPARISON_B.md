# T17 draft B comparison

`DraftB.lean` uses a Type-valued `CorrectionAPI`.  Its constants are data
chosen before the small scale `ε`, matching the registered A03/A05/I02 house
style.  The inputs are T16's concrete `CutoffData` and `LocalPotentialAPI` plus
T13's `LocalizationAPI`; T15 is neither imported nor restated.

## Paper clause to Lean field

| Paper clause | Draft B declaration/field | Registered `I02.*` counterpart |
|---|---|---|
| `eq:H`, lines 219–223 | `correctionForce` | V1 `force_formula` (its two middle additive terms are written in the opposite, equivalent order) |
| smooth zero extension, line 225 | `force_smooth`, `force_periodic` | V1 `force_smooth`; periodicity is new |
| spatial volume `O(ε³)`, line 225 | `force_support`, `force_spatial_volume` | V1 `force_support`, `force_spatial_volume` |
| temporal length `O(ε²)`, line 225 | `force_support`, `force_time_length` | V1 fields with the same names |
| first `eq:derivativebounds`, lines 225–228 | `correction_derivative_bound` | V1 field with the same name |
| second `eq:derivativebounds`, lines 229–230 | `force_derivative_bound` | V1 field with the same name |
| `eq:wE`, lines 232–234 | `correction_slice_memLp`, `correction_gradient_memLp`, `correction_energy_bound` | V1 fields with the same names, with T10's torus energy replacing the whole-space norm |
| `eq:Hmixed`, lines 235–237 | `correctionAlpha`, `mixedLebesgueENormT`, `force_spatial_memLp`, `force_mixed_bound` | V1 `alpha`, `force_spatial_memLp`, `force_mixed_bound` |
| `eq:HHs`, lines 238–240 | `sobolevConst_finite`, `force_sobolev_bound` | none: V1 explicitly excludes `eq:HHs` |
| constants uniform for small `ε`, line 242 | `D.ε₀`, `eps_le_one`, all constant data and finiteness fields | V1 `ε₀`, `eps_le_one`, constant fields |
| fixed-cylinder profile argument, lines 245–273 | `fixedProfileCylinder`, `rescaledReference`, `rescaledPotential`, `rescaledCorrectionProfile`, `rescaledForceProfile`, their identities/support/smoothness/uniform bounds | no contract field; implementation infrastructure exists in `CorrectionProfile` and `CorrectionForceProfile` |
| localization transfer, line 284 | `_localization : T13.Draft.LocalizationAPI` and `force_sobolev_bound` | none |

V2 adds only `prescribed_subset_plateau`; T16's `LocalPotentialAPI` already
contains the corresponding `K ⊆ D.plateau` clause, so T17 needs no second copy.

## Choices

- The fixed cylinder is exactly `[-2,2] × closedBall 0 D.θRadius`, which
  contains `tsupport D.η × tsupport D.θ` by T16.
- Uniform smoothness means the operator norm of every `iteratedFDeriv` order is
  bounded uniformly in `ε` on that cylinder.  Both `W_ε` and the exact
  bracketed force profile are included, together with their physical rescaling
  identities.
- `eq:Hmixed` uses a torus `Lp`-path norm modeled on registered
  `Data.mixedLebesgueENorm`; this handles `p=∞` and `q=∞` without changing the
  paper's range.  The bound uses `correctionAlpha p q + 1`, with
  `correctionAlpha` explicitly defined as `α=-3+3/p+2/q`.
- Norm bounds use finite `ENNReal` constants.  Energy and mixed bounds carry
  explicit `MemLp` fields; the Sobolev norm's integrability and measurable path
  are built into T10's datum-infimum definition.
- No rescaled T15 packet is mathematically used by this lemma.  The rescaled
  fields required by the proof are the reference `V_ε`, correction `W_ε`, and
  force profile; Draft B defines them explicitly from `v` and T16's cutoffs.

## Ambiguities

- T10 has `forceSobolevENormT` but no registered periodic mixed Lebesgue norm.
  Draft B supplies the direct Haar-measure analogue locally; reconciliation
  must decide whether it belongs in the T10 data contract.
- The manuscript says “spatial support has volume `O(ε³)`” without naming a
  time slice or projection.  Draft B follows I02 and measures the spatial
  projection of spacetime support, but does so on one torus copy.
- T13's localization API is charted in the fixed fundamental cube, whereas
  T16 stores a general coordinate ball about `x₀`.  The implementation must
  insert the appropriate torus translation/chart adapter.

## Needs a lemma

- Prove the two profile identities from T16's potential/correction formulas and
  parabolic differentiation.
- Turn joint profile smoothness on `[0,1]` times the compact cylinder into all
  uniform derivative constants and the two physical derivative bounds.
- Derive torus support volume/duration and `MemLp`/measurable-path witnesses
  from smooth compact support on one chart.
- Prove the periodic mixed-norm scaling, including both essential-supremum
  endpoints and the arithmetic identity
  `-2+3/p+2/q = correctionAlpha p q + 1`.
- Adapt each force slice to T13's `periodize` input, apply localization for
  `0<s<1`, use its endpoint fields at `s=0,1`, and integrate the resulting
  `ε^{3/2}` and `ε^{3/2-s}` rates in time.

## `Paper1` implementation candidates

- `CorrectionProfile`: `profile_smooth`, `profile_uniform_derivative_bound`,
  `profile_support`, `profile_uniform_global_derivative_bound`,
  `physicalCorrection_rescale`, `physicalCorrection_eq_profile`, and
  `physical_mixed_derivative_bound`.
- `CorrectionForceProfile`: `forceProfile`, `forceProfile_smooth`,
  `forceProfile_support`, `physicalForce_eq_profile`,
  `forceProfile_uniform_derivative_bound`, and
  `physicalForce_spatial_derivative_bound`.
- `CorrectionEnergy`: `physicalCorrection_uniform_energy` and
  `physicalCorrection_total_direction_energy`.
- `CorrectionMixedNorms`: `physical_force_spatial_memLp`,
  `physical_force_mixed_bound`, and `physical_force_mixed_memLp`.
- `CorrectionPositiveNorms` and `CorrectionVectorNorms`: the positive-order
  time estimates and vector assembly.
- `PeriodicCorrectionEndpointRates`:
  `correction_vector_whole_endpoint_rates` supplies the whole-space `s=0,1`
  rates before the T13 periodization adapter.
