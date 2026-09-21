# Lane 191 — A05 U4/U8 attempts and final route

## Result

`Section4/A05/RieszShift.lean` now constructs the physical field `Λv`, proves
that it stays in `MemHInfty`, proves that its order-`1/2` homogeneous datum is
the supplied order-`3/2` datum `Z` of `v`, and constructs the three derivative
data with the exact R43 Riesz-coordinate symbol.  The R43 wrapper in
`Section4/R43/ShiftedData.lean` supplies the complete `shifted` field of
`CriticalAdvectionLpBridge` for every interior classical velocity slice.

The independent `pairing_identity` field of that bridge is intentionally not
constructed here.

## U4: physical `Λv`

The physical carrier is

```text
rieszLambdaL2 v hv = -∑ j, R_j (∂_j v)
```

on the real vector `L²` space.  The multiplier used for `R_j` is exactly
`R43.rieszCoordinateSymbol j ξ = if ξ = 0 then 0 else I * (ξ j / ‖ξ‖)`.
The proof first builds the bounded complex Fourier multiplier, proves that it
commutes with translations, proves conjugate symmetry/reality preservation,
and transports it back to the real `L²` carrier.

Each derivative of an `H^∞` field has a smooth translation orbit.  A bounded
translation-commuting Riesz transform preserves that orbit, so
`EulerMeanSmoothRepresentative.smoothL2Field` produces a literal smooth real
field.  Its all-order square-integrable jets give
`rieszLambda_memHInfty`.

In Mathlib's cycles convention the derivative multiplier is `2πiξ_j`, hence

```text
-∑ j (i ξ_j / ‖ξ‖) (2π i ξ_j) = 2π ‖ξ‖
                                    = frequencyUnit * ‖ξ‖.
```

The normalized angular dilation is
`f(ξ) ↦ frequencyUnit^(-3/2) f(frequencyUnit⁻¹ ξ)`, so the transported
multiplier is exactly `‖ξ‖`, with no residual `2π`.

To compare with the supplied datum, the proof identifies a physical `L²`
component's angular Fourier distribution with
`angularFrequencyDilation (𝓕 g)`.  The `IsHomogeneousDatum (3/2)` pairing and
locally-integrable uniqueness then give

```text
angularVHat_i(ξ) = ‖ξ‖^(-3/2) Z_i(ξ)       a.e.
angularLambdaHat_i(ξ) = ‖ξ‖ angularVHat_i(ξ)
                      = ‖ξ‖^(-1/2) Z_i(ξ)  a.e.
```

This proves `rieszLambda_halfDatum`.  The generic theorem
`D01.Homogeneous.homogeneousDatum_unique` is valid at every real order, so the
special `a = 3/2` endpoint result anticipated in the brief was not needed.

The paper convention was checked directly at
`paper/sections/02-preliminaries.tex:49-60`, where
`Λ = (-Δ)^{1/2}` is fixed, and the R43 use was checked at
`paper/sections/04-whole-space.tex:95-110`.

## U8: derivative data

For each coordinate `j`, `derivativeHalfDatum j Z` multiplies every component
of `Z` by the exact token-for-token R43 symbol

```text
NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ.
```

`Paper3`'s distributional Fourier derivative formula contributes `2πiξ_j`.
The angular distribution dilation cancels `2π`, leaving `iξ_j`.  Against the
order-`3/2` realization,

```text
‖ξ‖^(-1/2) * (i ξ_j / ‖ξ‖) * Z_i
  = i ξ_j * ‖ξ‖^(-3/2) * Z_i.
```

This yields `derivativeHalfDatum_isDatum`; `derivativeHalfDatum_symbol` is the
literal a.e. multiplier statement consumed by R43.

## Packaging and R43 boundary

`shiftedCriticalData_of_memHInfty` packages U4 and U8.  Since
`ShiftedCriticalData v Z : Type`, Lean does not permit `theorem` syntax for a
constructor with that return type.  The requested name and exact type are
therefore exported as a `noncomputable def`.  The same applies to
`criticalAdvectionLpBridge_shifted`, whose result is a dependent function into
`ShiftedCriticalData`.

The exact diagnostic from attempting the requested syntax was:

```text
error: type of theorem
`NSFormalization.Section4.A05.shiftedCriticalData_of_memHInfty`
is not a proposition
```

For R43, `C01.velocity_slice_memHInfty` supplies the slice regularity and
`hcrit.velocityThreeHalf_isDatum` supplies `Z`.  Thus only fractional Parseval
remains before a full `CriticalAdvectionLpBridge` can be built.

## Discarded proof routes and diagnostics

1. Starting directly from `Source.FractionalRealization` gives an `L³`
   representative for orders strictly below `3/2`, but does not supply the
   literal `H^∞` physical `Λv` demanded here.  The translation-orbit route
   supplies the missing all-order jets.
2. Rewriting the canonical scalar component immediately by
   `componentLp_smoothField` initially failed because the two `MemLp` proofs
   were not definitionally the same.  The exact error was:

   ```text
   Tactic `rewrite` failed: Did not find an occurrence of the pattern
     componentLp ⋯ i
   ```

   An explicit equality using proof irrelevance and the named canonical
   smooth representative resolves the carrier mismatch.
3. Treating the angular dilation coefficient as an informal change of
   variables risks losing its `frequencyUnit^(-3/2)` normalization.  The final
   proof instead transports the a.e. cycles identity through the tree's exact
   `angularFrequencyDilation_coeFn` theorem and a proved
   quasi-measure-preserving dilation.

No `set_option maxHeartbeats` was needed.

## Satisfiability

`axioms_u4_u8.lean` contains the required zero example with `v := 0`, `Z := 0`.
It also uses the nonzero compact-smooth field

```text
x ↦ Cut.bump x • coordinateVector 0.
```

Its `MemHInfty` hypothesis is the restriction of standard compact-support jet
integrability, and its order-`3/2` datum is supplied by the standard theorem
`isHomogeneousSliceDatum_compact`.  Compact-smooth components are Schwartz, so
this is a genuine nonzero Schwartz satisfiability witness, not a zero-only or
unattained-premise check.
