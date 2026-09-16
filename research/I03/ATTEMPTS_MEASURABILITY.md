# Lane 255: compact homogeneous path measurability

## Result

The lane-250 input `CompactHomogeneousRealization` is now proved, with the
stronger statement that D01's concrete path is continuous on all of `ℝ`:

```lean
theorem compactHomogeneousPath_continuous {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s < 0) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Continuous (D01.Homogeneous.compactHomogeneousPath hs hF hc)
```

Consequently it is a.e. strongly measurable for `Data.forceTimeMeasure`, so
`compactHomogeneousRealization : CompactHomogeneousRealization` has no premise.

## Proof route

For two times `t,u`, homogeneous-datum uniqueness identifies

`compactHomogeneousPath hs hF hc t - compactHomogeneousPath hs hF hc u`

as the datum of the physical slice difference `x ↦ F(t,x)-F(u,x)`.  The
subtraction theorem needs the physical Schwartz-pairing integrability clauses;
these are supplied separately for the two compact Schwartz slices, rather than
assuming additivity of totalized integrals.

The exact norm of that datum is the angular homogeneous Fourier quantity.
`B02.lowHighSplit` then gives

```text
‖G(t)-G(u)‖² ≤ C_s · ‖F(t,·)-F(u,·)‖_{L¹}²
                    + ‖F(t,·)-F(u,·)‖_{L²}²,
C_s = (2π)⁻³ ∫_{|ξ|<1} |ξ|^{2s} dξ.
```

Here `-3/2 < s` is exactly the low-frequency integrability condition, while
`s ≤ 0` controls high frequencies.  `I02.continuous_slicePath` makes the
physical `L¹`- and `L²`-valued slice paths continuous using the common compact
spatial support.  The displayed majorant tends to zero as `t → u`, proving the
datum path continuous.

## Routes deliberately not used

* `R43.CriticalHomogeneous.ofSobolevVectorL` requires `0 ≤ s`; it cannot be
  applied at the negative orders here.
* Scalar norm measurability from lane 250 is not promoted to vector-valued path
  measurability; that implication is false without more structure.
* No measurable selection is taken from `IsHomogeneousSliceDatum`.  The proof
  stays with D01's explicit path and uses uniqueness only to estimate its
  difference.
* No new named hypothesis is needed.  Thus the satisfiability fallback was not
  invoked.

## Lean details

* Converting the `ℝ≥0∞` squared estimate to a real squared-norm estimate
  requires finiteness of both physical slice norms.  These come from
  `I02.slice_memLp` and are recorded before applying `ENNReal.toReal_mono`.
* `ENNReal.toReal_rpow` rewrites in the reverse direction when simplifying
  `(x ^ 2).toReal`.
* Strong measurability needs an explicit
  `SecondCountableTopologyEither ℝ (RealVectorSobolev s)` witness; using
  `⟨Or.inl inferInstance⟩` avoids an otherwise expensive typeclass search.
* The analytic module is upstream-only.  The exact lane-250 proposition and
  `HomogeneousScalingAPI` live downstream of Contracts, so their unconditional
  closure belongs in `verification/Bindings/ScalingHomogeneousClosed.lean`.

## Audit

`research/I03/axioms_path_measurability.lean` prints every declaration from the
new formalization and binding modules.  Every list is exactly
`[propext, Classical.choice, Quot.sound]`.  Its non-vacuity probes instantiate
continuity on an actual `PacketAPI` force and both homogeneous fields at
`q = 2`, `s = -1`.
