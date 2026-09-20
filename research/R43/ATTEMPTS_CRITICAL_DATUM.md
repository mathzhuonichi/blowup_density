# Lane 216 — attempts and resolution for `CriticalDatumPath`

## 1. Spatial datum construction

The successful construction starts with an inhomogeneous angular datum
`A : RealSobolevHilbert s`, for `s ≥ 0`, and applies the bounded multiplier

`|ξ|^s (1 + |ξ|²)^(-s/2)`.

`CriticalHomogeneous.ofSobolevScalar` proves that the result remains in the real
subspace. `ofSobolevScalar_isHomogeneousDatum` identifies its unweighted
distribution with the order-zero lowering of `A`, using
`weightedAngularFourier_realization`. The componentwise version and
`smoothAngularDatum` then give an order-`s` homogeneous datum for every smooth
field with square-integrable jets.

This closes all six slicewise carriers. In particular, `MemForceR` implies that
each nonnegative-time force slice has smooth square-integrable jets, so no extra
force-integrability input is needed for the G3 slicewise statement. This does
not by itself make the chosen homogeneous force path measurable or `L¹` in
time.

## 2. Spatial compatibility proofs

The order shift is proved by applying `homogeneous_slice_angular_ae` at orders
`1/2` and `3/2` to the same physical velocity component, then cancelling the
nonzero factor `|ξ|^{-3/2}` away from the null singleton `{0}`.

For the Laplacian symbol, the proof first expands the physical Laplacian field
as the sum of its three second directional derivatives. Two applications of
`A05.fourier_directionalField_component_ae` give the cycles-frequency symbol
`-frequencyUnit² |ξ|²`. The normalized angular dilation cancels
`frequencyUnit²`, yielding exactly `-|ξ|²`. A final common
`|ξ|^{-1/2}` cancellation transfers this physical Fourier identity to the two
chosen homogeneous data.

Velocity transversality and pressure longitudinality are transported from the
order-zero Fourier statements. The order-zero datum is first identified with
the normalized angular Fourier transform. The half-order datum differs by the
common radial factor `|ξ|^{1/2}`, so divergence-free and curl-free identities
survive after cancellation. The existing Leray multiplier lemmas then give the
two exact structure fields.

## 3. Time path and momentum attempt

The inhomogeneous A01 result `exists_differentiable_datumPath` was inspected as
the intended analogue. It differentiates a local-theory/Duhamel carrier and its
own report explicitly leaves the bridge from that representative to the
physical classical momentum residual open. An arbitrary `ClassicalSolutionR`
only stores continuous inhomogeneous datum paths; the tree contains no theorem
upgrading its velocity to a `C^∞` homogeneous order-`1/2` Hilbert-valued path.

Consequently the two time facts cannot currently be derived without adding new
time-dependent Fourier analysis beyond the available tree:

1. `ContDiffOn ℝ ∞ (criticalVelocityHalf w) (Ico 0 T)`;
2. the derivative of that path equals the four half-order momentum data on
   `Ioo 0 T`.

The fallback is one proposition, `CriticalDatumInputs w hf`, containing exactly
those two statements. It contains no spatial existence, Fourier symbol,
solenoidality, pressure, trilinear, pairing, or estimate assumption. The zero
classical solution with zero force inhabits it in
`axioms_critical_datum.lean`, so the restriction is non-vacuous.

## 4. Result

`criticalDatumPath` assembles the exact lane-175 structure from a classical
solution, `MemForceR`, and `CriticalDatumInputs`. `exists_criticalDatumPath`
packages it as `Nonempty`. `rcritical1_of_classical` applies lane 214 with the
assembled carrier and has no `hcrit` binder.

No alternative or weakened `CriticalDatumPath` structure was introduced.
