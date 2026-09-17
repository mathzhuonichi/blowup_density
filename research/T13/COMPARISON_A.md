# T13 draft A comparison — `lem:localization`

This is the independent draft-A statement audit for
`paper/sections/03-torus.tex:21-98`. It does not use any other T13/T10 draft or
brief.

## Paper clause → Lean field

| Paper clause | Lean declaration / field | Rendering choice |
|---|---|---|
| `03-torus.tex:34-39`, explicit `c_s` | `cFrac` | Extended-nonnegative Lebesgue integral of the same nonnegative integrand, with coordinate `0 : Fin 3` representing (h_1). |
| `03-torus.tex:43-48`, (I_{\mathbb R}(Z)) | `IReal` | Iterated `lintegral` on `Space = ℝ³`, for real three-vector fields; `‖·‖²` sums components. |
| `03-torus.tex:53-57`, (K_s) | `KFrac` | Literal `tsum` over `Lattice = Fin 3 → ℤ`, embedded by `PeriodicLocalization.lattice`. |
| `03-torus.tex:81-94`, nonzero lattice tail | `latticeTailSum` | Subtype-indexed `tsum` over `{n // n ≠ 0}` of the displayed (x-y+n) terms. |
| `03-torus.tex:61-67`, (I_{\mathbb T}(z)) | `ITorus` | Iterated integral over the concrete cube `[0,1]³` against `KFrac`; this makes (x-y) literal. |
| `03-torus.tex:40-51`, (I_{\mathbb R}=c_s\|Z\|_{\dot H^s(\mathbb R^3)}^2) | `LocalizationAPI.real_gagliardo_identity` | Uses registered `dotHomogeneousENorm`; quantifiers are `s`, field, range hypotheses, smoothness, compact support. |
| `03-torus.tex:58-72`, (I_{\mathbb T}=c_s\|z-\widehat z(0)\|_{\dot H^s(\mathbb T^3)}^2) | `LocalizationAPI.torus_gagliardo_identity` | Uses a local coefficient datum weighted by ‎‎(|2πk|^s); at `0 < s` the zero coefficient has weight zero, so subtracting the mean is implicit and exact. |
| `03-torus.tex:22-28`, `eq:localization` | `LocalizationAPI.uniform_localization` | One-sided (H^s(\mathbb T^3)) bound by the Euclidean (H^0+Ḋ^s) norms, exactly as printed. |
| `03-torus.tex:29,96-98`, endpoint rider | `LocalizationAPI.endpoint_identities` | Equality of squared (L^2) quantities at order zero and squared, component-summed gradient quantities at order one. |

The structure has exactly these four assertion fields: the two norm
identifications, localization, and endpoints. Kernel and norm declarations are
definitions, not extra mathematical assertions.

## Specification choices

### Periodic representation and (I_{\mathbb T})

The physical layer remains a function `Space → Space` with `UnitPeriods`, as
required by `SECTION3_PLAN.md` §1. `ITorus` is written on the cube rather than
on `UnitAddTorus`: the kernel is defined from a concrete difference (x-y),
and a torus difference has no preferred Euclidean representative. The
coefficient map is `Paper1.periodicFourierCoeff`, which already factors through
`torusLift` and normalized Haar measure; thus the analytic side still uses the
proved torus Fourier/Parseval bridge.

The chosen fundamental cube is `[0,1]³`, with open chart
`openFundamentalCube = (0,1)³`. `IsCoordinateBall B` means an actual Euclidean
metric ball, and the separate hypothesis
`closure B ⊆ openFundamentalCube` is the paper's strict-containment condition.

### Zero extension, support, and periodization

Instead of quantifying an additional local function `z`, the contract
quantifies its globally defined zero extension `zR` directly:

- `ContDiff ℝ ∞ zR`;
- `tsupport zR ⊆ B`, using topological support rather than merely
  `Function.support`;
- `zT = spatialPeriodization zR`, where `spatialPeriodization` is the actual
  lattice sum from `NavierStokes.PeriodicLocalization.periodize` applied to a
  time-independent spacetime field.

Because `closure B` lies in one chart, this is equivalent to the paper's
smooth `z` supported in `B`, zero-extended in that cube and then periodized.
It also avoids a weak predicate that merely assumes periodicity and agreement
on one copy.

Uniformity is represented by the exact quantifier order

```text
∀ B, ball/closure hypotheses → ∀ s, 0 < s → s < 1 →
  ∃ C : ℝ≥0, ∀ zR zT, support/periodization hypotheses → ...
```

so the same finite `C = C_{s,B}` applies to every smaller support inside the
fixed ball. The statement does not strengthen the paper to a reverse
inequality or equality.

### Scalar versus vector

Every API clause is stated for the paper's real three-vector physical field.
The Euclidean norm square in `IReal` and `ITorus` is the sum of the three
component squares. The Fourier norm uses

```lean
PiLp 2 (fun _ : Fin 3 => lp (fun _ : Fin 3 → ℤ => ℂ) 2)
```

so it has the same component-summed norm. The analytic scalar identity needed
in a proof is then applied componentwise. This choice matches the actual
packet/correction consumers and the vector convention in the registered
whole-space vocabulary.

### Norm and constant normalization

- Whole space: `dotHomogeneousENorm` is the registered angular-frequency,
  unitary-Fourier datum norm. No local copy is introduced.
- Torus homogeneous: the weight is exactly ‎(|2πk|^s), including the `2π`
  retained in `03-torus.tex:72`.
- Torus inhomogeneous: the weight is exactly
  ((1+|2πk|^2)^{s/2}=(1+4π^2|k|^2)^{s/2}).
- Fourier coefficients use probability Haar measure on the unit torus, hence
  no cube-volume factor occurs.
- `cFrac` uses the paper's displayed numerator and no hidden Fourier factor.
  All identities use this same constant.
- Nonnegative ordinary integrals are represented as `ℝ≥0∞` lintegrals. This
  composes with registered norms and preserves divergence as `⊤`; conversion
  to the paper's finite real `c_s` is a lemma after proving `0 < s < 1`.
- The Euclidean (L^2) summand in `eq:localization` is written
  `sobolevENorm 0 zR`. In the registered unitary normalization this is exactly
  (L^2), with the equality left as a bridge lemma.
- `C` is an `ℝ≥0`, so finiteness is built into its type. No positivity is
  added because the printed lemma only asserts the existence of a uniform
  constant and does not separately state `0 < C`.

## Ambiguities recorded

1. The lemma statement at `03-torus.tex:22-30` only prints the localization
   bound and endpoint rider; the two Gagliardo identities occur in its proof.
   The lane request explicitly requires all three analytic clauses, so they
   are separate structure fields.
2. The paper calls (B) a "coordinate ball" but does not fix whether the
   displayed fundamental cube is centered or `[0,1]³`. The existing cube/Haar
   bridge uses `[0,1]³`; translation gives the centered convention when
   needed.
3. The notation `supported in B` could mean nonzero support or topological
   support. Draft A chooses `tsupport zR ⊆ B`, the stronger standard analytic
   reading that guarantees separation from the cube boundary.
4. The proof writes scalar-looking absolute values but the surrounding
   section concerns vector fields. Draft A states the component-summed vector
   result; a scalar specialization/embedding is routine but not included as a
   fifth API field.
5. `03-torus.tex:67` explicitly writes `z - ẑ(0)`, while homogeneous
   coefficient norms commonly leave the zero mode unspecified. Draft A fixes
   it to zero through the positive-order weight, so the datum is unique.
6. `03-torus.tex:29` says "the corresponding equality" for gradients. Draft A
   interprets this as equality of the full squared (L^2) gradient norm,
   summed over spatial derivative directions and vector components.
7. The endpoint rider could be derived from a common local `z`; Draft A keeps
   the same `zR`/exact-periodization representation as the fractional clause
   so downstream consumers do not need a second support model.
8. The registered whole-space datum is reality-constrained, whereas the local
   periodic coefficient carrier is the full complex `ℓ²`. Reality follows
   from the physical real field but is not stored as a separate subtype; this
   does not change the norm, but T10 may choose to register the closed real
   subspace.

## Needs registration

- T10: `PeriodicVectorDatum`, angular frequency, periodic inhomogeneous and
  homogeneous datum predicates, and their fail-safe `ℝ≥0∞` norms.
- T13: the chosen open cube/chart predicate, coordinate-ball predicate,
  spatial periodization, radial kernel, `cFrac`, `KFrac`, lattice tail,
  Gagliardo integrals, and endpoint squared quantities.
- A later binding should identify the inhomogeneous local datum with
  `PeriodicSobolev.periodicFrequencyWeight` / `PeriodicSobolevHilbert` and
  identify its Fourier coefficient with the `torusLift`/Parseval layer.

## Needs a lemma / proof obligation

1. `cFrac_pos` and `cFrac_ne_top` for `0 < s < 1`, with the near-zero and
   far-field estimates of `03-torus.tex:35-39`.
2. Measurability of `fractionalRadialKernel`, `KFrac`, `latticeTailSum`, and
   both Gagliardo integrands.
3. The scalar whole-space Plancherel/Tonelli identity in the repository's
   angular unitary convention, then its finite-component vector sum.
4. Agreement of the literal compact-smooth Fourier integral with the
   registered `IsHomogeneousSliceDatum`/`dotHomogeneousENorm` norm.
5. The torus translation-difference Parseval identity, including interchange
   of the nonnegative lattice sum/integrals and the exact `2π` multiplier.
6. Existence and uniqueness of the weighted periodic `lp` datum for every
   smooth periodic field, at both the inhomogeneous and homogeneous weights.
7. The `PiLp 2` norm-square formula that turns the vector coefficient norm
   into the sum of scalar Fourier energies.
8. The zero-mode lemma: for `0 < s`, homogeneous weight at `k = 0` is zero and
   the norm equals that of `z - ẑ(0)`.
9. `sobolevENorm 0 zR = sqrt (wholeL2Sq zR)` for smooth compact real vector
   fields in the registered normalization.
10. Periodization regularity/periodicity and single-copy equality specialized
    from `PeriodicLocalization` to `spatialPeriodization`.
11. From `closure B ⊆ openFundamentalCube`, construct the positive boundary
    distance (d), prove the finite-near-lattice and summable-far-lattice tail
    bound uniformly for `x ∈ B`, `y ∈ Q`, and prove the reversed bound.
12. The `n = 0` comparison `ITorus ≤ IReal + tail`, including the fact that a
    nonzero integrand forces the corresponding point into `B`.
13. The concavity inequality `(1+r²)^s ≤ 1+r^(2s)` for `0 < s < 1`, followed
    by the square-root/triangle estimates that produce the printed norm bound.
14. Endpoint single-copy integral identities for the field and every spatial
    partial derivative.
