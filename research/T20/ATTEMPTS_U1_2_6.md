# T20 wave 1 mean reduction — lane 389

This note records the proof routes tried for U1 (`reductionRegular`), U2
(`meanBound`), and U6 (`meanFreeEquation`).  The canonical targets are copied
verbatim from `Section3/T20/CriticalRegularity.lean`; no replacement `Prop`
inputs, aliases, or repackaged goals were introduced.

## U1 — `reductionRegular`

The proof starts with a zero initial datum witness `a := 0`.  At a fixed time,
T11 `periodicMeanReductionAPI.mean_formula` identifies `meanPathT g t` with
the velocity spatial mean.  Thus `meanFreeVelocity` is definitionally the T10
`meanZeroPartT` of the velocity slice, while `meanFreeForce` is the same
mean-zero part of the force slice.  Smoothness and periodicity are preserved by
subtracting the constant mean.  The zero-mean clauses come from T11
`periodicMeanReductionAPI.transformed_mean_zero`; `MeanIdentity.meanT_translate`
transfers its Galilean-translated conclusions back to the untranslated fields.

The two fractional homogeneous memberships use the smooth periodic bridge
`NSFormalization.Section3.T13.periodicHomogeneousENorm_lt_top` (for orders
`1/2` and `3/2`), and `periodicSobolevENorm_ne_top_smooth` supplies the `H²`
membership.  The concrete `MemLp 2` conclusions for the force, gradient tensor,
and Laplacian come from smooth torus lifts (`memLp_torusLift_vector`,
`memLp_gradientTensor`, and `contDiff_laplacian`).  This is the T11
mean/reduction route with the mean formula; no critical T12 embedding is
required.

## U2 — `meanBound`

For a periodic datum `A` representing a slice `z`, the zero Fourier coefficient
has weight one.  A direct coefficient calculation proves
`‖meanT z‖ ≤ ‖A‖`; the proof uses
`periodicFourierCoeff_zero_eq_mean_component` and the `PiLp` norm formula.
The first inequality is the interval-integral norm inequality applied to
`meanPathT g t = ∫₀ᵗ forceMeanT g`, followed by
`ofReal_integral_eq_lintegral_ofReal`.  For the second inequality, unfold
`criticalRho` and `forceSobolevENormT`, compare the integral over `Ioc 0 t`
with the positive-time `Ioi 0` integral, apply the pointwise zero-mode bound to
every admissible Sobolev path, and finish with
`eLpNorm_one_eq_lintegral_enorm`.

## U6 — `meanFreeEquation`

At an interior time, T11's `mean_derivative` gives
`(meanPathT g)' = forceMeanT g`; `mean_formula` is used to rewrite the
solution mean to the data-defined path on a neighbourhood.  The T11 transport
slice lemmas (`temporalDerivative_eq_fderiv`, `advection_slice`,
`spatialDerivative_slice`, and `spatialLaplacian_slice`) show that subtracting
the spatially constant path removes the time derivative of the mean, leaves the
Laplacian and pressure gradient unchanged, and splits advection into
`advection v + (m · ∇)v`.  Rewriting the original pointwise momentum equation
then leaves `g - forceMeanT g`, which is exactly `meanFreeForce`.

## Residuals and failed routes

There is no residual theorem or named input for these three units.  Earlier
attempts that tried to obtain the mean-free regularity solely from a fractional
T12 embedding were unnecessary; smooth-periodic finiteness already supplies
the required totalized norms.  Likewise, the U2 estimate does not need a
finite-mode or critical embedding: only the zero-mode weight-one identity is
used.  No T12 `velocityCriticalL3`, `gradientLambdaCriticalL3`, or
`gradientLSix` field is consumed.

The resulting module is
`formalization/NSFormalization/Section3/T20/MeanReduction.lean`; exact-target
and non-vacuity checks are in
`research/T20/probes/mean_reduction_closes.lean`, and the guarded axiom audit is
in `research/T20/axioms_u1_2_6.lean`.
