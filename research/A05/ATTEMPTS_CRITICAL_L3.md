# A05 critical `L³` embedding — lane 165 attempts

This lane targets only `research/A05/Spec.lean:366`:

```lean
eLpNorm z 3 volume ≤
  ENNReal.ofReal criticalL3Const * dotHomogeneousENorm (1 / 2) z
```

The paper input is `paper/sections/04-whole-space.tex:105-112` and the
whole-space half of Lemma B.1.  The formal theorem is
`NSFormalization.Section4.A05.velocityCriticalL3` in
`Section4/A05/CriticalL3.lean`.  It uses a local copy of the datum infimum from
`research/R43/Spec.lean`; it never uses the pointwise-integral
`Contracts.V1.Data.dotHHalfENorm`.

## Route

Given an angular order-`a` homogeneous datum `G`, pull it back by the inverse
unitary angular-frequency dilation.  Its norm is still `‖G‖₂`.  The lemma
`u2_normalizedMultiplier_cyclesDatum` proves that the normalized cycles Riesz
multiplier of this pullback is exactly the Fourier transform of the tempered
distribution represented by `G`.

Take the cycles inverse Fourier transform as the `L²` input to
`Source.FractionalRealization.potentialOperator`.  Plancherel preserves its
norm.  Multiplication by `RieszKernelNormalization.coefficient a` cancels the
kernel coefficient in the commuting square.  Therefore the completed
potential representative is the original distribution and obeys

```lean
eLpNorm f (ENNReal.ofReal (targetExponent a)) volume ≤
  ENNReal.ofReal (scalarCriticalConst a) * ‖G‖ₑ
```

where

```lean
scalarCriticalConst a =
  RieszKernelNormalization.coefficient a *
    (potentialConstant a * 512 ^ (1 / targetExponent a)).
```

At `a = 1/2`, `targetExponent a = 3`.  Applying this componentwise and using
the finite-dimensional `ℓ² ≤ ℓ¹` estimate gives the explicit positive vector
constant

```lean
criticalL3Const = 3 * scalarCriticalConst (1 / 2).
```

Finally, if an order-half slice datum exists, D01's uniqueness theorem makes
the infimum equal its norm (`u1_dotHomogeneousENorm_eq`).  If no datum exists,
the infimum is `⊤`, and positivity of `criticalL3Const` makes the desired
inequality automatic.  Thus the statement is total without silently mapping a
missing datum to zero.

## Per-unit status

| unit | lane-165 status | exact result or residual |
|---|---|---|
| U1 | **closed for all real orders** | `u1_dotHomogeneousENorm_eq`: any `IsHomogeneousSliceDatum s z A` gives `dotHomogeneousENorm s z = ‖A‖ₑ`, using D01's already-proved uniqueness. |
| U2 | **closed for the critical route** | `cyclesHomogeneousDatum_norm`, `cyclesHomogeneousDatum_ae`, and `u2_normalizedMultiplier_cyclesDatum` give the exact angular-to-cycles multiplier identity, including the `frequencyUnit` normalization. |
| U3 | **supporting half closed; full row residual** | `u3_fourier_criticalInputFromDatum` and `u3_norm_criticalInputFromDatum` build the physical `L²` input from an already-given homogeneous datum and prove Plancherel norm equality.  Residual: prove the independent constructor `homogeneousLeSobolev` from an inhomogeneous `H^a` datum, plus the `a = 3/2` endpoint existence statement listed in the original U3 row.  `velocityCriticalL3` does not need that constructor: it branches on datum existence, and the datum norm is `⊤` in the empty case. |
| U4 | **residual; not used here** | Prove the full `research/A05/Spec.lean:300-315` `IsRieszPower` existence and norm fields for `0 < a ≤ 3/2`, including the endpoint.  This requires packaging an order-zero physical realization of each vector datum and showing it shares the same component datum. |
| U5 | **residual; not used here** | Prove the full `research/A05/Spec.lean:318-331` `IsBesselPower` existence and norm fields from paired order-`a` and order-zero inhomogeneous data. |
| U6 | **closed** | `u6_normalizedCriticalRealization_norm_le`, `u6_normalizedCriticalRealization_toDistribution`, and `u6_scalar_eLpNorm_le` prove the completion estimate and identify its physical representative with the original distribution for every `0 < a < 3/2`. |
| U7 | **closed for `velocityCriticalL3`; broader row residual** | `u7_targetExponent_half`, the component and sum lemmas, `u7_vector_eLpNorm_le_of_datum`, and `velocityCriticalL3` prove the requested real-three-vector `ℝ≥0∞` inequality.  The original U7 row also advertised the unused `a = 1` half of `embeddingPair` and a separately named `criticalRepresentative`; those wrappers are not delivered in this focused lane. |

The exact open signatures are therefore the U3 constructor/endpoint and the U4
and U5 relation APIs above.  None is an unsolved goal, axiom, or placeholder in
the delivered module.

## Failed and superseded approaches

1. A first monolithic proof combined scalar realization, distribution
   uniqueness, all three coordinates, and the ENNReal sum in one declaration.
   Lean stopped with the exact diagnostic:

   ```text
   error: (deterministic) timeout at `maxHeartbeats`, maximum number of heartbeats (400000) has been reached
   ```

   Splitting the route into `u6_*` and `u7_*` lemmas removed the timeout; the
   final module needs no `set_option maxHeartbeats` declaration.

2. Starting from `Contracts.V1.Data.dotHHalfENorm` was rejected before coding.
   Its defining pointwise Fourier integral totalizes to junk `0` away from its
   `L¹ ∩ L²` input assumptions.  The delivered theorem uses only the datum
   infimum, so missing realizations produce `⊤`, not `0`.

3. Trying to obtain U4/U5 as one-line applications of existing named theorems
   fails at name resolution: the searched source tree contains no declarations
   named `rieszPowerExists`, `rieszPowerNorm`, `besselPowerExists`, or
   `besselPowerNorm`; those names occur only as fields of the research draft
   API.  The corresponding probe diagnostic is:

   ```text
   error: Unknown identifier `rieszPowerExists`
   ```

   The required full search was made over
   `formalization/NSFormalization/{Section4,Paper1,Source}`.  The available
   lower-level ingredients are recorded in the U4/U5 residuals rather than
   being presented as completed relations.

4. The conformance witness was initially going to use the zero field.  It was
   strengthened to the concrete nonzero field
   `x ↦ Cut.bump x • coordinateVector 0`.  Smoothness, compact support,
   datum-form `MemHInfty`, nonzeroness, and application of
   `velocityCriticalL3` are all checked in
   `research/A05/axioms_critical_l3.lean`.

## Axiom result

All nineteen exported theorems and all five named non-vacuity witness theorems
print exactly

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorry`, `admit`, `axiom`, or `native_decide` in the module or the
audit file.
