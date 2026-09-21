# T12 double-blind draft B comparison

## Scope and representation

`DraftB.lean` follows the Section 3 representation decision: a physical field is
a unit-periodic function on `Space = EuclideanSpace ℝ (Fin 3)`, while its analytic
datum is a weighted `lp (Fin 3 → ℤ) 2` sequence.  Three components are assembled
with `WithLp 2`, so the vector norm is the square-sum convention of
`01-introduction.tex:103`, rather than the default supremum norm on a Pi type.

The definitions from `SpatialField` through `IsPeriodicLambda` are local draft
copies.  They need registration in, or definitional bridges to, T10.  In
particular, the inhomogeneous multiplier is exactly
`(1 + 4π²|k|²)^(s/2)` and the homogeneous multiplier is `|2πk|^s`, with
the zero mode omitted.

## Paper clause to Lean field

| Paper clause | Lean field | Quantifiers and formulation |
|---|---|---|
| `appendix-a-local-theory.tex:8-12`, `eq:Rproduct`, `||vw||_{H^m} <= C_m(...)`, `m >= 2` | `MeanZeroSobolevAPI.tameProduct` | `K.product` is fixed first; then `m`, its lower-bound proof, the two physical scalar fields, and their `H^m` memberships. The result is the literal pointwise product. No mean-zero hypothesis is imposed. |
| `appendix-a-local-theory.tex:12`, `||v||_infinity <= C||v||_{H^2}` | `boundedRepresentative` | Essential-supremum `L^∞` norm on the torus; `v` is a physical `H^2` representative. This clause is inhomogeneous and does not require mean zero. |
| `appendix-b-embeddings.tex:11-24,26-29`, periodic `||v||_3 <= C||v||_{dot H^(1/2)}` | `velocityCriticalL3` | `MemPeriodicHomogeneous (1/2) v` explicitly contains unit periodicity, `L^2`, vanishing `k=0` coefficient, and finiteness of the homogeneous datum norm. The constant is independent of frequency support. |
| `appendix-a-local-theory.tex:22-26` and `appendix-b-embeddings.tex:26-31`, `||nabla v||_3 + ||Lambda v||_3 <= C||v||_{dot H^(3/2)}` | `gradientLambdaCriticalL3` | One field for the one displayed sum inequality. `Lv` is a physical representative pinned by `IsPeriodicLambda v Lv`, i.e. by the `|2πk|` multiplier. |
| `appendix-b-embeddings.tex:26-33`, used at `03-torus.tex:470-477`, `||nabla v||_6 <= C||Delta v||_2` | `gradientLSix` | Smooth unit-periodic, mean-zero physical vector field; Frobenius gradient and componentwise Laplacian. |
| `03-torus.tex:490-500`, `||v||_{H^2} <= C||Delta v||_2` | `hTwo_le_laplacian` | Smooth unit-periodic, mean-zero physical vector field. This is separate from the critical embedding because it is the exact continuation input. |
| `02-preliminaries.tex:50-54` and `appendix-b-embeddings.tex:85-90`, equivalence of `H^s` and `dot H^s` from the gap at `k != 0` | `spectralGap` | For every `s >= 0`, a mean-zero field with finite homogeneous datum satisfies `H^s <= K.gap s * dot H^s`. |

There are exactly seven inequality fields in the API.  Positivity is attached to
the seven constant families/values in `MeanZeroSobolevConstants`.

## Choices made

- Norms are `ℝ≥0∞`-valued.  An absent Fourier datum gives `top`; no `.toReal`
  conversion can turn an infinite quantity into a spurious zero.
- `IsPeriodicSobolevDatum` and `IsPeriodicHomogeneousDatum` relate the physical
  field directly to its weighted Fourier coefficients.  The norm is the
  infimum of witness norms, matching the robust datum style of
  `verification/Contracts/V1/Data.lean`.
- `IsMeanZero` is literally the T10-plan condition that the `k = 0`
  coefficient vanishes.  `meanZeroPart` is also recorded physically as
  `z - integral_T3 z`.
- Critical homogeneous norms are total only on mean-zero representatives.
  Thus no nonzero constant field can satisfy `velocityCriticalL3` via a
  zero homogeneous seminorm.
- The two terms at order `3/2` remain one inequality because the manuscript
  displays their sum under one constant.
- `eq:Rproduct` is stated for scalars.  This is the literal multiplication
  clause; the paper's componentwise vector/tensor consequences can be derived
  after component-norm lemmas are available and are not extra T12 target
  fields.
- The derivative clauses use smooth physical representatives, the class used
  by the paper's Navier--Stokes application.  The basic `H^(1/2) -> L^3`
  clause is stated on any physical representative with finite homogeneous
  datum, not merely on a Fourier polynomial.
- Lean does not generate non-proof projections from a `Prop`-valued
  structure.  To retain the requested `MeanZeroSobolevAPI ... : Prop` and
  still expose universal real constants, the constants and positivity proofs
  are fields of `MeanZeroSobolevConstants`, and the API is parameterized by
  that record.  The record is fixed before any theorem-field quantifiers.

## Ambiguities to reconcile

1. `appendix-b-embeddings.tex:21` says "periodic distributions", while the
   Section 3 representation decision keeps physical fields on `R^3`.  At the
   positive orders used here every embedded object has an `L^2` representative;
   draft B states that representative form.  An accepted contract could instead
   make distributional derivative witnesses explicit.
2. `02-preliminaries.tex:53-54` says equivalence at "each fixed order", while
   the displayed spectral-gap calculation in
   `appendix-b-embeddings.tex:85-90` is made for `a in {1/2,1}` and the T12
   continuation also needs order `2`.  Draft B states the natural common
   positive-order result `s >= 0`.  Restricting it to `{1/2,1,3/2,2}` would be
   sufficient for all current consumers.
3. `eq:Rproduct` uses generic notation `v w`; its proof says the argument is
   componentwise for vectors and tensors.  Draft B makes the displayed
   multiplication theorem scalar and leaves scalar-vector/tensor assembly as
   derived lemmas.  If the accepted contract is intended to expose those
   consumers directly, they should be added as explicitly labelled derived
   interfaces, not silently folded into the paper clause.
4. The manuscript gives no canonical numerical constants.  Draft B uses one
   independent positive constant for each displayed inequality (and a family
   for the order-dependent clauses).  Sharing a constant between distinct
   displays would be stronger and is unnecessary.
5. `IsPeriodicLambda` identifies a chosen smooth physical representative by
   all Fourier coefficients.  A registered T10 multiplier may instead return
   the representative as an operator; the two spellings require a bridge.

## Needs a lemma

- T10 definitional bridges for `torusLift`, the frequency lattice, weighted
  vector `lp` data, Fourier coefficients, inhomogeneous/homogeneous norms,
  mean, mean-zero part, and the `Lambda` multiplier.
- Parseval/uniqueness for vector coefficient data, including equality between
  the `WithLp 2` datum norm and the manuscript's sum of the three component
  squares.
- The zero-coefficient/integral equivalence and
  `periodicFourierCoeff (meanZeroPart z) i 0 = 0`.
- Spectral-gap comparison of the inhomogeneous and homogeneous weights,
  summed in `lp`, uniformly in the field and its frequency support.
- Periodic convolution/Young estimates and the lattice
  `sum (1 + 4π²|k|²)^(-2) < infinity` needed for `eq:Rproduct` and
  `H^2 -> L^∞`, followed by the physical representative/reconstruction
  bridge.
- A genuinely uniform mean-zero `dot H^(1/2)(T^3) -> L^3(T^3)` theorem.
  `PeriodicFiniteCriticalInterface.lean` and
  `PeriodicCriticalBridge.lean` retain a cardinality or finite inverse-weight
  loss and therefore cannot discharge this field.
- Fourier multiplier identities for physical partial derivatives, `Lambda`,
  and the Laplacian, including preservation of the zero mode.
- Componentwise assembly of the half-order embedding to obtain the combined
  gradient/`Lambda` `L^3` estimate.
- The mean-zero `H^1 -> L^6` estimate plus the Fourier identity comparing the
  Hessian and Laplacian norms, yielding `gradientLSix`.
- The order-two Poincare/spectral identity yielding
  `hTwo_le_laplacian`.
- Measurability and `MemLp` bridges between physical periodic fields, their
  canonical torus lifts, and the `eLpNorm` quantities in the API.

Existing periodic assets are partial inputs only:
`Paper1/TorusCube.lean` supplies the scalar torus lift and Parseval;
`PeriodicSobolevHilbert.lean` supplies a weighted scalar datum for orders up to
one; `PeriodicMeanZero.lean` identifies the zero coefficient;
`PeriodicMeanZeroEstimate.lean` is finite-spectral;
`PeriodicH2Embedding.lean` proves inverse-weight lattice summability but does
not finish a physical `H^2 -> L^∞` theorem; and
`PeriodicCompactSobolevL6.lean` treats compact periodizations rather than all
mean-zero periodic fields.

## Section 4 counterparts

- A03 tame product: `verification/Contracts/V1/TameProduct.lean`, especially
  `TameProductAPI.tameProductScalar` (with scalar-vector/tensor consequences in
  the same contract).
- A03 bounded representative:
  `verification/Contracts/V1/BoundedRepresentative.lean`, especially
  `BoundedRepresentativeAPI.eLpNormTop_le`.
- A05 gradient `L^6`: `verification/Contracts/V1/GradientL6.lean`, especially
  `GradientL6API.gradientLSix` and its Hessian/Laplacian identity.
- A05 velocity critical `L^3`:
  `verification/Contracts/V2/GradientL6.lean`, field
  `GradientL6V2API.velocityCriticalL3`, supported by the datum norm in
  `verification/Contracts/V1/HomogeneousNorm.lean`.
- There is no registered Section 4 field matching the combined
  `||nabla v||_3 + ||Lambda v||_3` display, and no whole-space analogue of the
  torus spectral-gap or `H^2 <= C||Delta v||_2` clauses (low frequency prevents
  the latter on `R^3`).
