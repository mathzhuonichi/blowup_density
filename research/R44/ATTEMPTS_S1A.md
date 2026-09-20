# R44 S1a attempts — lane 218

## Result

`formalization/NSFormalization/Section4/R44/JWeight.lean` closes the datum-level
S1a row with one satisfiable structure, `JWeightDatum u f`.  It provides:

- `Jmul`, its weighted-carrier symbol, its physical unweighted symbol, and its
  exact norm / extended-norm isometry;
- the paper spellings `Y`, `Z`, `B`, with `Z` defined through A03's existing
  one-vector `gradientSobolevENorm`;
- `weight_identity`, including the equality of `Z²` with the sum of the three
  derivative datum norm squares;
- `force_pairing_le` and `force_pairing_le'` at the genuine negative-order
  carrier `RealVectorSobolev (-1/2)`.

## Carrier normalization correction

The literal first draft requested a total map

```lean
RealVectorSobolev s → RealVectorSobolev (s - 1)
```

whose *stored* `FourierData` is multiplied by `(1+|ξ|²)^(1/2)` and whose norm
is unchanged.  Those two requirements are incompatible in this repository.
`RealVectorSobolev s` stores the already weighted datum
`(1+|ξ|²)^(s/2) û`; it is not a raw Fourier-transform carrier.  Multiplication
of an arbitrary stored `L²` datum by the unbounded square-root weight is neither
total on `L²` nor norm preserving.

The correct physical map `J : H^s → H^(s-1)` leaves the stored weighted datum
unchanged:

```text
(1+|ξ|²)^((s-1)/2) · [(1+|ξ|²)^(1/2) û]
  = (1+|ξ|²)^(s/2) û.
```

Accordingly `Jmul_weighted_symbol` is the carrier identity, while
`Jmul_symbol` removes the order weight on both sides and then states the usual
physical multiplier `(1+|ξ|²)^(1/2)`.  This is the only interpretation that is
simultaneously total and an exact isometry on `RealVectorSobolev`.

## Weight identity route

An initial direct `lintegral` proof duplicated analysis already present in
`D01/FiniteOrderNorm.lean`.  The final proof reuses its sharp theorem
`norm_raise_sq_eq`.  From the half-order velocity datum and the three
half-order weak-derivative data, D01 constructs the order-three-halves raised
datum and proves exactly

```text
‖raise A‖² = ‖A‖² + ∑ j, ‖C j‖².
```

Datum uniqueness identifies `raise A` with the supplied `H^(3/2)` datum.
`sobolevENorm_eq_of_isSobolevDatum` then turns all four datum norms into the
paper's infimum-defined Sobolev norms.  No new analytic premise is left open.

## Force duality route

Negative real orders are supported without a fallback definition:
`RealVectorSobolev (-1/2)` is the same complete weighted `L²` carrier with a
different realization.  The force datum stores `(1+|ξ|²)^(-1/4) f̂`, while
`Jmul velocityThreeHalf` stores the `H^(1/2)` datum of `Ju`, namely
`(1+|ξ|²)^(3/4) û`.  Their real Hilbert pairing is therefore the Fourier
duality pairing.  `abs_real_inner_le_norm`, followed by `weight_identity`, gives
the square-root form.  The elementary `sqrt (Y²+Z²) ≤ Y+Z` gives the paper's
second form.

## Satisfiability

`research/R44/axioms_s1a.lean` constructs both:

- the all-zero `JWeightDatum`; and
- a nonzero compact-smooth velocity
  `x ↦ Cut.bump x • coordinateVector 0`, with standard `smoothAngularDatum`
  realizations at orders `1/2` and `3/2`, standard half-order data for all
  three derivatives, the standard weak integration-by-parts pairing, and zero
  force at order `-1/2`.

Thus the one named structure is a restriction of standard Sobolev realization
properties satisfiable by nonzero Schwartz-type data.

## Failed proof-engineering paths

1. Defining the literal stored-data square-root multiplier was rejected for the
   mathematical reason above, before encoding an unbounded partial operator.
2. Building derivative data by rewriting the dependent order
   `(3/2)-1 = 1/2` introduced proof transports that made the non-vacuity audit
   brittle.  Constructing the same unique derivative data directly with
   `smoothAngularDatum` avoided casts and kept the witness standard.
3. The first `Z` spelling used an ad hoc square root of a sum.  It was replaced
   by A03's canonical `gradientSobolevENorm`; `Z_sq_eq_sum_norm` proves the two
   spellings equal using the supplied finite data.

No `sorry`, `admit`, `axiom`, `native_decide`, or heartbeat override is used.
