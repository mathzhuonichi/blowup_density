# T12 spectral-gap proof attempts (lane 300)

## Paths used

- Imported `NSFormalization.Section3.T10.DatumBasics` as the sole member of
  the mutually incompatible T10 proof-module trio.  The proof uses
  `periodicFourierCoeff_zero_eq_mean_component` at the zero mode.  It does not
  import `Parseval` or `PhysicalBridge`.
- Proved the lattice estimate by choosing a coordinate `i` with `k i ≠ 0`,
  using `Int.one_le_abs`, and bounding that coordinate's square by the finite
  sum.  This gives `4 * π^2 ≤ periodicAngularFrequencySq k` for `k ≠ 0`.
- Built `reweightDatum` directly on the nested carrier
  `WithLp 2 (Fin 3 → lp (fun _ : PeriodicFrequency ↦ ℂ) 2)`.  Inner membership
  is `Memℓp.mono'`; the inner norm estimate is `lp.norm_mono`; the outer norm
  estimate is obtained from `PiLp.norm_sq_eq_of_L2`.
- For `homogeneous_le_sobolev`, mapped every inhomogeneous datum into a
  homogeneous datum and used `le_iInf`.  Thus an empty inhomogeneous witness
  family is handled automatically: the right side is `⊤`.
- For `spectralGap`, extracted a homogeneous witness from
  `periodicHomogeneousENorm s v ≠ ⊤`, mapped it to an inhomogeneous datum, and
  used coefficientwise uniqueness to identify the homogeneous infimum with
  that witness's extended norm.

## Resolved elaboration errors (exact text)

The first direct invocation preceded building its imported canonical module:

```text
error: object file '.../formalization/.lake/build/lib/lean/NSFormalization/Section3/T12/MeanZeroCalculus.olean' of module NSFormalization.Section3.T12.MeanZeroCalculus does not exist
```

This was resolved by building `MeanZeroCalculus` and `DatumBasics` from
`verification/` before direct elaboration.

The first zero-mode weight branch left the nonnegativity goal unreduced:

```text
error: unsolved goals
case pos
s : ℝ
hs : 0 ≤ s
⊢ 0 ≤ periodicFrequencyWeight 0 ^ (s / 2)
```

It was resolved by applying `Real.rpow_nonneg` to the separately proved strict
positivity of `periodicFrequencyWeight`.

The first generic reweighting term did not constrain the comparison sequence's
type sufficiently:

```text
error: typeclass instance problem is stuck
  SeminormedAddGroup ?m.59
```

It was resolved by naming the fully typed fact
`hmem : Memℓp (fun k : PeriodicFrequency ↦ (C : ℂ) • A i k) 2` before calling
`Memℓp.mono'`.

The first zero-field probe omitted the local probability instance and produced:

```text
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsFiniteMeasure periodicTorusMeasure
```

The probe now declares both instances with explicit names:
`spectralGapProbeUnitAddCircleMeasureSpace` and
`spectralGapProbeUnitAddCircleProbability`.

## Residual hypotheses or gaps

None.  There is no residual named hypothesis beyond the exact API binders
`hs : 0 ≤ s` and `hv : MemPeriodicHomogeneous s v`.  No alternate analytic
Parseval or physical-reconstruction hypothesis is used.
