# Lane 214 — fractional Parseval

## Successful route

The result is unconditional relative to `CriticalDatumPath w hf`. No new
named analytic hypothesis is necessary. The physical field in the conclusion
is precisely `(criticalAdvectionLpBridge_shifted hcrit t ht).lambda`.

1. `homogeneous_slice_angular_ae` identifies an arbitrary supplied homogeneous
   slice datum with the normalized angular Fourier transform of the canonical
   component `L²` class. It uses `isSliceDistribution_unique` and lane 191's
   `homogeneousDatum_angularFourier_ae`; no pointwise Fourier integral of a
   potentially non-`L¹` field is used.
2. `angular_real_parseval` takes real parts of the complex `L²` inner products.
   Both `angularFrequencyDilation.inner_map_map` and `Lp.inner_fourier_eq`
   preserve that pairing. `real_inner_eq_re_complex` handles the actual real
   `L²` instance, as explained in `D01/RealPairing.lean`.
3. `half_order_parseval` proves the more general identity
   `inner A B = ∫ x, inner (u x) (rieszLambda v hv x)` for `u ∈ L²`,
   `v ∈ MemHInfty`, and their supplied half-order homogeneous data `A, B`.
   Lane 191's `angular_rieszLambda_component_ae` supplies exactly `|ξ|`,
   without a residual `2π` factor. Away from the null singleton `{0}`, the
   two inverse half-weights cancel that symbol:
   `|ξ| * (|ξ|^(-1/2) * |ξ|^(-1/2)) = 1`.
4. `component_real_pairing` converts each component class back to the physical
   real integral. `MemLp.integrable_mul` justifies commuting the finite sum
   with the integral. Thus the proof does not rely on the default value of
   a nonintegrable Bochner integral.
5. `D01.advection_slice_smoothL2` and `A03.SmoothL2.memLp` supply the advection
   slice's `L²` membership. The advection of the stationary lift is
   definitionally the original spatial advection slice. The specialization
   `pairing_identity_of_hcrit` therefore has exactly the required field type.
6. The bridge constructor uses lane 191's `shifted` unchanged; the primed
   trilinear and differential-inequality corollaries instantiate lane 182.

## Searches and discarded directions

The brief's `Paper3/RealPairing*` glob has no matching file in this checkout.
The relevant real-inner-product bridge is in `Section4/D01/RealPairing.lean`.
`Source/PhysicalRemoval.lean` concerns spatial/temporal cutoff removal, not
Plancherel. `Source/FractionalRealization.lean` and
`Source/FractionalRepresentative.lean` supply potential representatives but
are not needed: lane 191 already identifies the actual scalar `L²` Fourier
classes of its chosen smooth Riesz realization. Mathlib's applicable
Plancherel theorem is `MeasureTheory.Lp.inner_fourier_eq` in
`Mathlib/Analysis/Fourier/LpSpace.lean`.

Initial elaboration diagnostics and fixes:

- `Ambiguous term SpatialField`, with interpretations
  `D01.Homogeneous.SpatialField` and `A02.SpatialField`.
  Fix: open only the two required homogeneous declarations.
- `‖ξ‖ * ‖ξ‖⁻¹ = 1` did not directly elaborate as
  `‖ξ‖ * ‖ξ‖ ^ (-1) = 1` after `norm_num`.
  Fix: `simpa only [Real.rpow_neg_one] using mul_inv_cancel₀ hn.ne'`.
- The scalar field of `EuclideanSpace.proj i` was underdetermined in the
  component integrability proof. Fix: specify `(𝕜 := ℝ)`.
- `integral_finset_sum` is deprecated at this pin. Use `integral_finsetSum`.

No heartbeat override, admission, added axiom, or extra hypothesis was used.

## Satisfiability and scope

`axioms_parseval.lean` constructs all fields of `CriticalDatumPath` for
`A04.zeroSol 1 2`, invokes the new bridge constructor, obtains both primed
corollaries at `t = 1`, and instantiates the exact Parseval conclusion with
lane 191's shifted field. It supplies neither an independent bridge nor a
trilinear estimate. All eight module declarations and the audit's zero-path
constructor print exactly `[propext, Classical.choice, Quot.sound]`.

The general lemma imposes only standard `L²`/`H^∞` and homogeneous-datum
properties, so it does not restrict the fields to zero, stationary, compact,
or `L¹` cases. Constructing `CriticalDatumPath` from the classical solution
alone remains outside this lane. S1b's additional bridge is closed; this does
not assert that every remaining R43 obligation is closed.
