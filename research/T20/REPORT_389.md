# Lane 389 — T20 U1/U2/U6 report

## 1. Theorems proved

`NSFormalization.Section3.T20.reductionRegular`, `meanBound`, and
`meanFreeEquation` are proved with the exact field statements from
`Section3/T20/CriticalRegularity.lean`.

- `reductionRegular` establishes the smooth, periodic, mean-zero reduction and
  all stated `Ḣ^{1/2}`, `Ḣ^{3/2}`, `H²`, gradient, Laplacian, and force `L²`
  finiteness clauses.  It uses T11 `mean_formula`, `transformed_mean_zero`,
  translation invariance of the mean, and smooth periodic torus bridges.
- `meanBound` proves the interval bound for the mean path and the upper bound
  by `criticalRho`, using the zero Fourier mode's weight-one estimate and the
  admissible-path infimum in `forceSobolevENormT`.
- `meanFreeEquation` differentiates the data-defined mean using T11
  `mean_derivative`, applies the transport slice identities, and subtracts the
  force mean from the classical momentum equation, retaining the required
  `(m · ∇)v` term.

No named `Prop` input or T12 critical embedding is required.  There is no
residual for these three units.  The remaining W1 units U3/U4/U5 are outside
this lane.

## 2. Lean contents

- `formalization/NSFormalization/Section3/T20/MeanReduction.lean` — the three
  theorem declarations in namespace `NSFormalization.Section3.T20`.
- `research/T20/probes/mean_reduction_closes.lean` — verbatim target-shape
  examples closed by `exact reductionRegular`, `exact meanBound`, and `exact
  meanFreeEquation`; it also exhibits a nonzero `coordinateVector 0` constant
  mode, its `torusConstantDatum`, and the inhabited zero force class.
- `research/T20/axioms_u1_2_6.lean` — guarded `#print axioms` audit for all
  three theorems.
- `research/T20/ATTEMPTS_U1_2_6.md` — route and residual log.
- `research/T20/T20_SPLIT.md` — lane-389 DONE status entry.

No new `instance` declarations were added (so there are no anonymous-instance
name collisions); all local constructions are explicit terms and all imported
instances remain the canonical named ones.

## 3. Remaining gaps

U1, U2, and U6 are complete and unblocked.  U3 (`bIntegral`), U4
(`constantTransportSkew`), and U5 (`constantTransportCommutesLambda`) remain
for other W1 lanes.  The later critical path still depends on the T12
`velocityCriticalL3`, `gradientLambdaCriticalL3`, and `gradientLSix` fields as
recorded in `T20_SPLIT.md`; none is assumed here.

## 4. Commands and results

The Lean commands were run from `verification/` with `LEAN_NUM_THREADS=6`:

```text
lake build NSFormalization.Section3.T20.MeanReduction   ✔ 0 errors
lake env lean ../formalization/NSFormalization/Section3/T20/MeanReduction.lean   ✔
lake env lean ../research/T20/probes/mean_reduction_closes.lean                 ✔
lake env lean ../research/T20/axioms_u1_2_6.lean                                 ✔
```

From the repository root, `LEAN_NUM_THREADS=6 make check` also exits 0.

The axiom audit prints, for each of `reductionRegular`, `meanBound`, and
`meanFreeEquation`, exactly:

```text
[propext, Classical.choice, Quot.sound]
```

`make check` is run before handoff; its result is recorded with the committed
lane.  No `sorry`, `admit`, `axiom`, `native_decide`, or placeholder declaration
is present.
