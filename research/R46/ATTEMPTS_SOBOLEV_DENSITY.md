# Proposition 4.6 first clause — proof record

Lane 256 proves `REnergyAPI.completedSobolevDensity` directly, without an
additional named hypothesis.

## Successful route

1. Apply `Bindings.bochnerPartial.approxCompact` at radius `r / 2` to obtain a
   compact smooth force `g`, an order-`s` datum path `Dg`, and
   `bochnerDatumENorm q s (Dg - b) < r / 2`.
2. Apply `Bindings.density_compact` at radius `r / 2` to obtain
   `f ∈ breakdownSetIn forceClassCompact ν a T` with
   `forceSobolevENorm q s (f - g) < r / 2`.
3. Unfold `forceSobolevENorm` and use `iInf_lt_iff` to extract a measurable
   Sobolev path `E` of `f - g` whose Bochner norm is below `r / 2`.
4. Use `DatumLemmasAPI.isSobolevPath_add` on `g + (f - g) = f`.  Its two
   integrability side conditions follow from `F_c ⊆ F_R` and
   `DatumLemmasAPI.memForceR_slice_integrable`; the condition for `f - g` is
   obtained by subtracting the integrable pairings for `f` and `g`.
5. Take `D = Dg + E`.  After rewriting
   `(Dg + E) - b = E + (Dg - b)`, `eLpNorm_add_le` and
   `ENNReal.add_halves` give the strict radius bound.

The strict-addition lemma `ENNReal.add_lt_add` makes the last step valid even
when the caller chooses `r = ⊤`: both summands are then individually finite,
so their sum is still strictly below `⊤`.

## Points checked and rejected as unnecessary

- No separate compact-subtraction lemma is needed.  Path additivity only asks
  for integrability of the physical slices, which follows by subtracting the
  two registered `F_R` slice pairings.
- No explicit compact-force datum constructor is needed for `f - g`; the
  strict infimum inequality already contains a subtype witness after
  `iInf_lt_iff`.
- No satisfiability hypothesis is isolated: both anticipated difficult steps
  (path additivity and infimum extraction) are available in the current tree.
