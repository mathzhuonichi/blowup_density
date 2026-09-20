# Lane 170 — C01 rows E6/E7 attempts and result

## Result

Rows E6, E7, and the exact `enstrophyIdentity` assembly are closed in
`Section4/C01/EnstrophyIdentity.lean`, without placeholders and with exactly the standard
three transitive axioms.

1. `laplacianField_divergence_zero` proves that `Δu` is divergence free from
   `curl (curl u) = ∇(div u) - Δu` and `div (curl v) = 0`.
2. `laplacian_pressure_pairing_zero` feeds that fact, the packaged pressure gradient, and
   pressure smoothness to the existing `gradient_pairing_zero` theorem.
3. `inner_enstrophy_identity_deriv` is the carrier-independent E7 algebra.  Substitution of
   `Gt = νL - N - P + F` into `d = -2⟪L,Gt⟫` produces
   `d = 2⟪N,L⟫ - 2ν‖L‖² - 2⟪F,L⟫`.
4. `enstrophyIdentity_classical` combines E5, E6, E7, and `momentum_split_toLp` in raw
   carrier-B integral vocabulary.  `enstrophyIdentity_gradientSq` transports it to the local
   copies of the spec vocabulary (`gradientSq`, `advectionWork`, `laplacianSq`, `pairing`,
   `A05.lap`).
5. `h2TimeIntegral_strict` proves the C01 rpow lower integral is finite whenever `0 < S < T`.
   The order-two datum path from `ClassicalSolutionR.sobolev` is continuous on `[0,S]`, hence
   its squared norm is integrable there; `A04.sobolevENorm_eq` identifies the ENNReal
   integrand.  `squaredHTwoIntegral_strict` is the A04 npow spelling, obtained through lane
   159's `R43.enorm_npow_two_eq_rpow_two`.  The absorption-shaped theorem has the exact
   registered gate
   `ENNReal.ofReal A05.gradientL6Const * criticalL3 (slice u t) ≤ ENNReal.ofReal (ν/4)`;
   this gate is logically unnecessary on a strict compact subinterval.

## Attempts and pitfalls

### Pressure cancellation

Applying `gradient_pairing_zero` directly with the velocity proves only the order-zero
pressure cancellation `⟪∇p,u⟫ = 0`.  E6 needs its second argument to be `Δu`.  The missing
input is therefore pointwise `div (Δu) = 0`, not another pairing theorem.

The first vector-identity normalization attempt left

```text
Laplacian.laplacian U.field - gradient 0 = -vectorCurl (vectorCurl U.field)
```

because `gradient 0` did not simplify under the function equality.  An explicit function
equality `gradient (0 : Space → ℝ) = 0` followed by `zero_sub` gives the stable orientation.
For the outer negation, rewriting `divergence_eq_coordinate_sum` on both the goal and
`divergence_curl`, then simplifying `fderiv_neg`, `PiLp.neg_apply`, and
`Finset.sum_neg_distrib`, avoids searching for a separate divergence-linearity lemma.

### Spec-vocabulary bridge

A large `simpa` unfolded the outer `laplacianField` sum but stopped at the nested carrier
field:

```text
(fderiv ℝ ((velocitySliceField ...).directionalField ...).field x) ...
```

while `A05.lap` contained the definitionally equal `A05.dirDeriv`.  The robust bridge is to
first prove whole-field equalities using the existing
`laplacianField_velocitySlice_field`/`advectionField_velocitySlice_field`, rewrite those
into the raw identity, and only then unfold the five local spec definitions.

### Strict-interior lower integral

Routing the ENNReal integral through a real continuous squared norm was shorter than proving
a time-axis `MemLp` statement.  `lintegral_ofReal_ne_top_iff_integrable` consumes the
ordinary `IntegrableOn` result, and the pointwise rewrite uses
`A04.sobolevENorm_eq`, `ENNReal.rpow_two`, `ofReal_norm`, and `ENNReal.ofReal_pow`.

## Exact residual

The spec's quantitative `h2TimeIntegral` field is **not** proved.  In particular, the current
theorem requires `S < T`, while the spec permits `S ≤ T`; the endpoint is the one needed at a
hypothetical maximal lifespan.  The retained probe
`research/C01/probes/e7_endpoint_probe.lean` records the exact failure:

```text
Application type mismatch: The argument
  hST
has type
  S ≤ T
but is expected to have type
  S < T
in the application
  h2TimeIntegral_strict w hS hST
```

Before recording absence, the required search was run with `grep -rn` over all of
`Section4/{D01,A03,A04,A05,A01,C01}`.  There is no implementation of the two remaining
assembly inputs; the same probe reports:

```text
Unknown identifier `sobolevTwoFourier`
Unknown identifier `enstrophyIntegralBound`
```

Thus this lane does not obtain the explicit `ENNReal.ofReal (Cassembly * ...)` bound, the
`S = T` endpoint, or `h2TimeIntegralZeroDatum`.  The residual is analytic rather than a
missing scalar Grönwall lemma: prove the integrated absorbed estimate
`enstrophyIntegralBound`, then prove the carrier-crossing order-two inequality
`sobolevTwoFourier`; combine them with the already registered `l2Bound` and
`forceTimeRegularity`.

## C01 V4 registration plan

Do not register a contract in this lane.  A future C01 V4 should extend the frozen V3 record.
The exact `enstrophyIdentity` field is ready to add now.  Once the residuals above close, the
same V4 should add `enstrophyDifferentialBound`, `enstrophyIntegralBound`,
`sobolevTwoFourier`, `h2TimeIntegral`, and `h2TimeIntegralZeroDatum` token-for-token from
`research/C01/Spec.lean`.  The strict-interior finiteness lemma is a proved precursor, not a
replacement for the quantitative spec field.
