# T11 — lead amendments to the proof plan (`T11_SPLIT.md`)

## Amendment 1 (2026-09-18 01:30Z): the named local-existence input gets order-wise force bounds

Lane 311 (`EXISTENCE_ROUTE.md` §"Residual input and a quantifier issue") showed that the input of `T11_SPLIT.md` §1 U9,
`PeriodicQuantitativeLocalInput`, cannot be instantiated by U10: it demands one bound `K` for `forceSobolevENormT 1 m g` **at every order `m`**, while a smooth
compactly supported force only has a finite norm at each order separately (a single nonzero mode times a time bump has norms growing like `W(k)^(m/2)`).

**Decision.** Replace the input by the order-wise version; the local time `δ` may depend on `ν`, the `H¹` datum bound `K`, and the whole family of force bounds:

```lean
def PeriodicQuantitativeLocalInput' : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
          ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
```

This is exactly what U10 can instantiate: for a fixed `f ∈ forceClassT` and `S ≥ 0`, the shifts `timeShiftT t₀ f`, `t₀ ∈ Icc 0 S`, have
`forceSobolevENormT 1 m (timeShiftT t₀ f) ≤ forceSobolevENormT 1 m f =: M m` at every order (translation invariance of the time integral — prove it in U10), and
`M m ≠ ⊤` by lane 312 (T10 item 11). It is also what Appendix A proves: the existence time depends on the datum norm and on (finitely many) force norms.
U9b–e prove `PeriodicQuantitativeLocalInput'`; lane 311's `quantitative_lifespan_lower_bound` is re-derived from the primed input in U9b (one-line change).
The `H¹` ball itself stays as stated (risk §3 of the split unchanged).
