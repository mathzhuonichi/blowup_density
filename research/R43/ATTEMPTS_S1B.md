# R43 S1b attempts — critical trilinear estimate

Date: 2026-09-15. Lane: `182-R43-s1b-trilinear`.

## 1. Base-state discrepancy

The task brief says this worktree contains lane 175's
`Section4/R43/CriticalPairing.lean` and
`research/R43/REVIEW_175-R43-s1-pairing.md`. At lane start neither path existed
at `HEAD` or at `origin/erenup/integration`. The accepted commits were reachable
on `origin/erenup/175-R43-s1-pairing`:

```text
a6fac76 Prove R43 critical pairing identities
861c295 [175-R43] Add codex review (ACCEPT) and probes
```

The accepted `CriticalPairing.lean` was therefore restored byte-for-byte as a
new prerequisite file. The review was read with `git show`; it was not copied.
No merge or rebase was performed.

## 2. What the available interface proves

At a fixed time write

```text
A = hcrit.velocityHalf t
Z = hcrit.velocityThreeHalf t
N = hcrit.advectionHalf t.
```

`CriticalDatumPath` provides:

- `A` as the order-`1/2` datum of `u(t)`;
- `Z` as the order-`3/2` datum of `u(t)` and the a.e. symbol `Z=|ξ|A`;
- `N` as the order-`1/2` datum of `(u·∇)u`.

The new module proves the remaining inequality layer:

- three-factor `L³` Hölder in `ℝ≥0∞`;
- the vector embedding for any supplied half-order datum;
- `‖∇v‖₃+‖Λv‖₃ ≤ 4 C_{1/2} ‖Z‖₂` from the exact coordinate
  Riesz symbols `i ξ_j/|ξ|`;
- the final estimate with
  `trilinearConst = C_{1/2}(4C_{1/2})² = 16 C_{1/2}³`.

## 3. The exact residual carrier bridge

The following mandated whole-tree search was run before declaring a missing
export:

```text
grep -rnE "derivativeCriticalL3|IsRieszPower|rieszPowerExists|rieszPowerNorm|homogeneous.*partialDeriv|partialDeriv.*homogeneous|IsHomogeneousSliceDatum.*dirDeriv|dirDeriv.*IsHomogeneousSliceDatum|CriticalTrilinearEstimate|advectionHalf" \
  formalization/NSFormalization/Section4/A05 \
  formalization/NSFormalization/Section4/B02 \
  formalization/NSFormalization/Section4/D01 \
  formalization/NSFormalization/Section4/A03 \
  formalization/NSFormalization/Section4/C01 \
  formalization/NSFormalization/Section4/R43 \
  formalization/NSFormalization/Source \
  formalization/NSFormalization/Paper1
```

It found only A05's docstring saying U4 is residual and the lane-175 datum
fields/use sites. There is no physical `Λu` constructor, homogeneous derivative
datum constructor, `IsRieszPower`, or fractional Parseval bridge in those
directories. This agrees with:

- `research/A05/ATTEMPTS_CRITICAL_L3.md`: U4 residual;
- `research/A05/COMPARISON.md` rows U4 and U8;
- `research/A05/REVIEW_165-A05-critical-l3.md`: the wrappers are absent even
  though scalar U6 is available.

Accordingly the module isolates one named hypothesis:

```lean
structure CriticalAdvectionLpBridge (hcrit : CriticalDatumPath w hf) where
  shifted : ∀ t ∈ Ioo 0 T,
    ShiftedCriticalData (fun x => w.velocity (t, x))
      (hcrit.velocityThreeHalf t)
  pairing_identity : ∀ t (ht : t ∈ Ioo 0 T),
    ⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
      ∫ x, ⟪(u·∇)u(t,x), (shifted t ht).lambda x⟫
```

`ShiftedCriticalData` contains only carrier facts: the physical `Λv` field and
its half-order datum `Z`, the three physical derivative half-data, and their
exact a.e. symbols

```text
D_j,i(ξ) = (i ξ_j/|ξ|) Z_i(ξ).
```

It contains no `L³` or trilinear estimate. The multiplier norm bound, all
embeddings, Hölder, and the final estimate are theorems. The zero-solution
example in `axioms_s1b.lean` constructs this bridge, so it is consistent and
the conditional theorem is non-vacuous.

An unconditional

```lean
∀ hcrit, CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit
```

still requires constructing `CriticalAdvectionLpBridge hcrit`. Concretely: Constructing `shifted` requires the unexported A05 U4/U8 carriers (plus `MemHInfty` closure for `Λu`), while `pairing_identity` is a separate fractional Parseval/duality obligation. (`shifted`: an endpoint physical realization for `Z` and homogeneous derivative data with the displayed Riesz symbols; `pairing_identity`: the Parseval identity extending the Schwartz/L² Fourier pairing to the `L³ × L³ × L³` product.) No Lean compiler
goal remains inside the conditional theorem.

## 4. Elaborator diagnostics encountered and resolved

The first draft used a nonexistent order helper:

```text
Unknown identifier `mul_le_mul_left'`
```

It was replaced by `mul_le_mul' le_rfl ...`.

The first three-factor Hölder normalization used the real-norm rewrite rather
than the extended norm rewrite:

```text
⊢ eLpNorm (fun x => ‖f x‖ₑ) 3 volume * ... =
    eLpNorm f 3 volume * ...
```

The correct lemma is `MeasureTheory.eLpNorm_enorm`.

The first Riesz-symbol norm proof left the absolute value of the denominator:

```text
(div_le_one hnorm).mpr hcoord
has type |ξ j| / ‖ξ‖ ≤ 1
but is expected to have type |ξ j| / |‖ξ‖| ≤ 1
```

It is now normalized with `abs_of_pos hnorm`. All three issues are resolved.
