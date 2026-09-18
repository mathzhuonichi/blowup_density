# T11 implementation candidates

This survey is declaration-based.  Candidates were found with `rg` over
`formalization/NSFormalization/Paper1/Periodic*.lean` and
`vendor/HeliCorgi/Formal/*.lean`, then their statements were read at the cited
lines.  A candidate is not claimed to prove the T11 field; the last column is
the exact adapter or mathematics still missing.

## `PeriodicLocalRegularity`

| API field | closest existing declaration | statement gap |
|---|---|---|
| `sobolev_smooth` | `Paper1/PeriodicSmoothSobolev.lean:45`, `smoothPeriodicWeightedFourierLp` | Produces one scalar weighted Fourier datum from one globally smooth periodic spatial field at one order.  T11 needs a vector datum path representing every solution slice and `ContDiffOn` of that path in time, for every integer order. |
| `pressure_poisson` | `Paper1/PeriodicPressureSymbolOperator.lean:37`, `laplaceOperator_pressureOperator` | Solves a raw coefficient-level Poisson equation under a zero-mode premise.  It supplies neither a physical pressure reconstruction nor the T11 source `div f - div div(u⊗u)`, endpoint smoothness, periodicity, or gauge identification. |
| `projected` | `Paper1/PeriodicPressureRecoveryBridge.lean:71`, `normalizedFlow_equation` | Gives the normalized full residual equation for `PeriodicLifespan.Flow`.  The field still needs the `ClassicalSolutionT ↔ Flow` conversion and the physical identity `convectionDivergenceT = advection` under solenoidality to rewrite the residual into T11's projected form.  `PeriodicPressureFlowBridge.lean:77` (`normalized_flow_witness_of_residual`) packages the same bridge but assumes an existing flow. |

## `PeriodicLocalTheoryAPI`

| API field | closest existing declaration | statement gap |
|---|---|---|
| `horizon` | `Paper1/PeriodicLocalLifespan.lean:73`, `ClassicalPeriodicLocalTheory.local_flow`; for an explicit nonperiodic model, `vendor/HeliCorgi/Formal/R3QuantitativeLifespan.lean:44`, `r3MildLifespan` | The periodic interface only returns an existential horizon and is itself a conditional `Prop`; it does not select a function `ν → a → f → ℝ`.  The HeliCorgi horizon is explicit but is unforced whole-space H³ mild theory, not the torus `initialClassT`/`forceClassT` theory. |
| `solution` | `Paper1/PeriodicLocalLifespan.lean:84`, `exists_periodic_local_flow_of_classicalTheory` | Conditional on `ClassicalPeriodicLocalTheory` and returns `PeriodicLifespan.Flow` on some horizon.  T11 needs an unconditional `ClassicalSolutionT` on the selected common horizon, with T10 Sobolev and pressure-gauge fields. |
| `regularity` | `Paper1/PeriodicLifespan.lean:12`, `Flow`, together with `Paper1/PeriodicSmoothSobolev.lean:45`, `smoothPeriodicWeightedFourierLp` | `Flow` carries slab smoothness, periodicity, divergence and the residual, but no smooth Fourier-datum path, Poisson pressure clause, or projected equation record.  The Fourier theorem is slice-local/scalar and is not connected to `Flow`. |
| `velocity_unique` | `Paper1/PeriodicLocalLifespan.lean:175`, `flow_velocity_agree_on_common_interval` | The pointwise common-interval conclusion matches, but is stated for `Flow`; a fieldwise `ClassicalSolutionT ↔ Flow` conversion is required. |
| `pressure_unique` | `Paper1/PeriodicLocalLifespan.lean:229`, `normalized_flows_agree` | Gives literal pressure equality only for two `IsNormalized` `Flow`s.  The adapter must translate T10's Haar gauge to `cubeIntegral` normalization and convert both solution structures. |
| `horizon_le_lifespan` | `Paper1/PeriodicLifespan.lean:30`, `horizon_le_lifespan` | The supremum argument is exact in shape, but uses `Flow` and `lifespan`; T11 needs the conversion theorem and equality with `maximalLifespanT`. |
| `exists_maximal` | `Paper1/PeriodicLocalLifespan.lean:491`, `exists_maximal_periodic_solution` | Conditional on `ClassicalPeriodicLocalTheory`, different admissibility/force predicates, and returns the Type-valued `MaximalSolution`.  T11 asks for fields satisfying `IsMaximalPeriodicSolution` over `ClassicalSolutionT`. |
| `maximal_unique` | `Paper1/PeriodicLocalLifespan.lean:515`, `maximal_solutions_agree` | Agreement is already presingular and includes normalized pressure, but is parametrized by `MaximalSolution` and an auxiliary horizon `S`.  It must be transported to arbitrary field pairs satisfying T11's predicate and specialized directly at each `t`. |

`Paper1/PeriodicOrdinaryLocal.lean:53`,
`exists_finiteOrder_local_of_representative`, is not a viable replacement for
`solution`: it assumes `OrdinaryRepresentative` (`:33`), whose field has genuine
whole-space `L²(ℝ³)` jets.  The module itself records at `:13-16` that a
nonzero periodic field cannot generally supply this.  It is useful only as a
finite-order solver after an impossible-for-general-periodic-data premise.

## `PeriodicContinuationAPI`

| API field | closest existing declaration | statement gap |
|---|---|---|
| `restart` | `vendor/HeliCorgi/Formal/R3QuantitativeLifespan.lean:193`, `r3EndpointSafeProjected_exists_mildSolutionOn_mildLifespan`; restart identity at `vendor/HeliCorgi/Formal/EndpointSafeTwoSpaceRestart.lean:185` | Gives norm-controlled local H³ mild existence and a time-shift identity in unforced whole-space carrier vocabulary.  T11 requires one `δ` uniform over all torus restart times and all `H¹`-bounded classical data for the shifted fixed force, plus `PeriodicLocalRegularity`. |
| `higherOrderBound` | `Paper1/PeriodicSmoothSobolev.lean:45`, `smoothPeriodicWeightedFourierLp`; closest Grönwall pattern `vendor/HeliCorgi/Formal/R3TSelBridge.lean:256`, `r3TSel_carrierBound_of_ladder` | The periodic theorem gives existence of each slice datum but no uniform-in-time bound.  HeliCorgi bounds only the whole-space H³ carrier and assumes a separate ladder plus a gradient integral; it does not derive every integer-order torus bound from finite squared H² energy. |
| `restartBeyond` | `Paper1/PeriodicLocalLifespan.lean:535`, `exists_periodic_extension_of_finite_h2`; abstract endpoint mechanism `vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:59` | The periodic theorem assumes a full `Flow` at horizon `S` and `FiniteH2Energy`, rather than common fields solving every `b<S`, a uniform H¹ trajectory bound, and `δ` chosen before the datum.  The HeliCorgi theorem explains the endpoint choice but leaves restart existence as a structure field. |
| `extendsBeyond` | `Paper1/PeriodicLocalLifespan.lean:535`, `exists_periodic_extension_of_finite_h2`; overlap helper `:564`, `extension_agrees_on_common_interval` | It has the desired larger normalized flow and overlap, but requires an attained `Flow ... S`.  T11 deliberately permits an unattained endpoint through `SolvesBelowT`; it also uses an `ℝ≥0∞` datum norm, so a bridge to `FiniteH2Energy` and the solution conversion are needed. |
| `lifespanInfiniteOfLocallyFinite` | `Paper1/PeriodicLocalLifespan.lean:583`, `maximal_endpoint_gt_of_finite_h2` | Proves one strict endpoint inequality from one full flow and `FiniteH2Energy`.  T11 needs to instantiate it at every real `S ≤ maximalLifespanT`, handle a potentially unattained endpoint via `SolvesBelowT`, bridge both lifespan notions, and conclude equality with `⊤`. |

The elementary restriction layer already exists:
`Paper1/PeriodicFlowRestriction.lean:20` (`Flow.restrict`) and `:48`
(`Flow.nonempty_restrict`).  The criterion-measure adapter starts at
`Paper1/PeriodicFiniteH2Bridge.lean:25`, but none of those declarations equates
`squaredHTwoIntegralT ≠ ⊤` with `FiniteH2Energy`.

## `PeriodicMeanReductionAPI`

| API field | closest existing declaration | statement gap |
|---|---|---|
| `mean_formula` | `Paper1/PeriodicMeanZero.lean:15`, `periodicFourierCoeff_zero_eq_cubeIntegral` | Identifies the zero Fourier mode with one scalar cube integral.  It does not integrate the Navier–Stokes equation, prove vanishing means for Laplacian/pressure/nonlinearity, or derive `mean u(t) = mean a + ∫ mean f`. |
| `mean_derivative` | `Paper1/PeriodicPressureNormalization.lean:149`, `pressureMean_hasDerivAt_interior` | This is a scalar differentiation-under-the-cube-integral theorem for pressure.  T11 needs the componentwise vector velocity mean and must use the PDE cancellations to identify its derivative with the force mean. |
| `transformed_solution` | `Paper1/PeriodicPressureNormalization.lean:237`, `normalizedFlow` | This is the closest existing solution-preserving transformation, but it only subtracts the pressure mean.  There is no Galilean/time-dependent translation module; proving the field requires chain rules, `X'=m`, transformed residual/divergence/gauge, solution conversion, and full regularity. |
| `transformed_classes` | `Paper1/PeriodicInitialData.lean:59`, `Flow.initial_admissible`, and `Paper1/PeriodicLocalLifespan.lean:39`, `IsTestForce.to_smoothPeriodic` | These establish the untransformed datum/force class facts in older vocabulary.  They do not show that subtracting the datum mean and translating/subtracting the force mean preserves T10's exact global smoothness, periodicity and compact positive-time support. |
| `transformed_mean_zero` | `Paper1/PeriodicPressureNormalization.lean:254`, `normalizedFlow_mean_zero` | Proves zero mean for normalized pressure only.  T11 requires Haar-zero mean of the centered initial velocity, Galilean velocity, and Galilean force at every solution time. |
| `translation_preserves_sobolev` | `vendor/HeliCorgi/Formal/R3YoungL1L2Bochner.lean:37`, `norm_r3L2Translate` | Proves translation isometry only for whole-space `L²` velocity.  T11 needs every real-order periodic weighted Fourier extended norm, including the no-datum `⊤` case. |

The grep found no `Galilean`, `PeriodicMeanReduction`, or solution-mean
evolution declaration in the surveyed files.  The six fields therefore form a
coherent new proof package rather than adapters around an existing Galilean
API.

## `PeriodicViscosityRescalingAPI`

| API field | closest existing declaration | statement gap |
|---|---|---|
| `scaled_classes` | `Paper1/PeriodicUniqueness.lean:43`, `normalized_smooth`, and `:51`, `normalized_periodic` | These prove slab smoothness and spatial periodicity for the same amplitude/time rescaling.  They do not package `initialClassT` or `forceClassT`, prove divergence preservation, or track the force's compact positive-time support. |
| `inverse_identities` | `Paper1/PeriodicUniqueness.lean:19`, `normalized_residual` | This is the nearest consumer of the same rescaling formulas.  No inverse-composition declaration was found; the three full-function identities still require field extensionality and positive-ν algebra. |
| `to_unit` | `Paper1/PeriodicUniqueness.lean:19`, `normalized_residual`, plus `normalized_smooth`/`normalized_periodic` at `:43`/`:51` | The PDE residual, smoothness and periodicity scaling ingredients exist, but no theorem constructs a unit-viscosity `Flow` or `ClassicalSolutionT`.  Initial value, divergence, Sobolev data, pressure gauge, class preservation and `PeriodicLocalRegularity` remain. |
| `from_unit` | `Paper1/PeriodicUniqueness.lean:19`, `normalized_residual` | Only the forward normalization identity is packaged.  There is no inverse solution constructor; all `ClassicalSolutionT` fields, horizon transport, exact restored fields, gauge and regularity must be rebuilt. |

No viscosity-scaling declaration was found in `vendor/HeliCorgi/Formal/*`.
The strongest local HeliCorgi results (`R3QuantitativeLifespan.lean:193` and
`:211`) keep arbitrary positive viscosity rather than reducing it to one.
