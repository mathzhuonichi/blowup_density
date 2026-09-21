# D01 gap G1: datum-form `dotHomogeneousENorm`

## The three reconciled specifications

| file | local declaration | role and difference |
|---|---|---|
| `research/A05/Spec.lean:131-132` | `def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ := ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ` | The original general-order, slicewise quantity for Lemma B.1. It lives in `BlowupDensity.A05.Draft`; the surrounding draft also defines the embedding relations and estimates. |
| `research/R43/Spec.lean:142-143` | exactly the same two token lines | A deliberate local copy in `BlowupDensity.R43.Draft`. Its documentation explicitly pins the name and arity to A05 rather than specializing the definition to `s = 1/2`; Proposition 4.3 consumes the `1/2` instance, while the general arity stays compatible with A05's additional consumers. |
| `research/R44/Spec.lean:47-67` | no local definition | This is intentional, not a third competing spelling. Proposition 4.4 fixes the initial velocity to `fun _ => 0` and uses the time-integrated **inhomogeneous** force norm `forceSobolevENormL2 (-1/2)`. The spec says explicitly at lines 52-54 that there is no spatial homogeneous norm in this statement. |

Thus A05 and R43 agree character-for-character on the definition; only their
namespaces, docstrings, and consumers differ.  R44 has nothing to reconcile at
the declaration level.  The promoted definition keeps the shared general-order
name and arity in `NSFormalization.Section4.D01`, with a verbatim version-1
contract copy in `BlowupDensity.Contracts.V1.HomogeneousNorm`.

The type is an infimum over **datum witnesses**, not over vector distributions
and not over pointwise Fourier integrals.  A witness
`G : RealVectorSobolev s` carries three real-symmetry-constrained `L²` frequency
components; `IsHomogeneousSliceDatum s z G` says that a tempered vector
distribution representing the physical field has homogeneous datum `G`.
Consequently the right-hand side is already in the datum norm consumed by
`Paper1/SchwartzCriticalEmbedding.lean:57` and `:171`: both estimates are
bounded by the `L²` norm of the fractional derivative datum, not by a separately
totalized physical Fourier integral.

## Why `dotHHalfENorm` and `dotHThreeHalvesENorm` are unusable here

`Contracts/V1/Data.lean:407-430` defines
`homogeneousFourierENorm` by applying the pointwise Bochner transform
`angularFourier` to each physical component and integrating
`|ξ|^(2s) |ẑ(ξ)|²`.  `dotHHalfENorm` and
`dotHThreeHalvesENorm` are only abbreviations of that quantity at `s = 1/2` and
`s = 3/2`.

That form is faithful for the `L¹ ∩ L²` slices named in its own docstring
(Schwartz and smooth compactly supported fields).  A general smooth `H^∞`
field is in `L²` but need not be in `L¹`.  Mathlib's Bochner integral is
totalized: when the pointwise Fourier integral is not integrable, it returns
zero.  Hence `angularFourier` can be junk zero on precisely the non-`L¹` fields
to which R43/A05 apply, making a critical smallness hypothesis accidentally
true.  The datum predicate instead uses the distributional angular transform;
for the `L²` fields in the manuscript classes, pairing with every Schwartz test
is integrable.  If no order-`s` homogeneous datum exists, the empty ENNReal
infimum is `⊤`, so the smallness test fails safely.

No equation with either V1 quantity is asserted.  Equality can be established
on the special `L¹ ∩ L²`/Schwartz domain using the existing homogeneous
witness results, but it is not the general physical-field definition.

## Proved basic interface

The new implementation module proves:

* `dotHomogeneousENorm_le_of_isHomogeneousSlice hG :
  dotHomogeneousENorm s z ≤ ‖G‖ₑ`;
* `le_of_isHomogeneousSlice hG`, the requested short spelling of the same bound;
* `dotHomogeneousENorm_zero (s) : dotHomogeneousENorm s 0 = 0`;
* `dotHomogeneousENorm_ne_top_of_isHomogeneousSlice hG :
  dotHomogeneousENorm s z ≠ ⊤`;
* `dotHomogeneousENorm_ne_top : (∃ G, IsHomogeneousSliceDatum s z G) →
  dotHomogeneousENorm s z ≠ ⊤`.

The zero proof constructs the zero tempered vector distribution and zero datum;
the upper-bound and finiteness proofs are direct consequences of the infimum.

## Attempted reuse and the intentionally open comparison

`Section4/D01/HomogeneousWitness.lean` provides the definitionally compatible
homogeneous predicate, uniqueness, zero-compatible algebra, and witnesses for
Schwartz/compact fields.  `Section4/B02/*` and
`Contracts/V2/HomogeneousPartial.lean` reuse that predicate for homogeneous
approximation, but do not turn a general inhomogeneous datum into a homogeneous
one.  `Section4/D01/SmoothDatum.lean` supplies the matching infimum shape for
`sobolevENorm`, which is why the G1 definition and elementary infimum lemmas are
short.

The tempting additional statement

```lean
0 ≤ s → dotHomogeneousENorm s z ≤ sobolevENorm s z
```

is mathematically correct but is not a short order-theoretic lemma about the two
infima.  It first needs a map from every order-`s` inhomogeneous datum `A` to the
homogeneous datum
`|ξ|^s (1+|ξ|²)^(-s/2) A`, its contraction bound, preservation of the
real subspace, and the distributional realization identity through
`Paper3.weightedAngularFourier_realization`.  `Section4/D01/HalfOrder.lean:38-56`
records exactly this missing construction and assigns it to the already-open G2
and homogeneous half of G3.  Claiming the inequality merely from finiteness of
both infima would omit the essential relationship between their unique data.
It is therefore not asserted by this G1 lane.

## Contract placement

The mathematical restatement is the new version-1 contract
`verification/Contracts/V1/HomogeneousNorm.lean`, importing only
`Contracts.V1.Data`; the binding theorem is `rfl`.  Creating this new V1 file
registers version 1 of the new component without changing any pre-existing
frozen V1 declaration.
