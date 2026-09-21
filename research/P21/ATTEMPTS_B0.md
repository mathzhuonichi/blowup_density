# P21 Route B / B0 attempts

Lane 503 closes B0 on both domains.  No residual is hidden behind a named
input, and no critical-smallness estimate from `Section3/T20/H1Energy.lean`
is used.

## 1. Normalization and carriers

The registered inhomogeneous Fourier weight is `(1 + |ξ|²)^s`.  Consequently

```text
H¹² = L²² + gradient²
H²² = L²² + 2 gradient² + Hessian²
     = H¹² + gradient² + Hessian².
```

The tempting formula `H²² = H¹² + Hessian²` is false for this normalization.
Both new modules state the coefficient `2` and the corrected recurrence
explicitly.

On `R³`, the proof constructs the real angular datum componentwise from
`D01.Homogeneous.compactSchwartzComponents` and `Paper3.angularDatum`.
Conjugate-reflection symmetry puts each component in `RealSobolevHilbert`;
`angularRealization_datum` proves physical realization, and datum uniqueness
collapses the registered infimum.  The scalar recurrence
`Source.angular_succ_energy` then gives the physical first- and second-order
energies.

On `T³`, `T10.smooth_periodic_datum` supplies the registered carrier,
`T17.norm_datum_eq_sqrt` identifies its norm with the scalar Fourier sums, and
`Paper1.periodicSobolevSq_nat` identifies those sums with
`periodicIntegerEnergy`.  Orders one and two unfold to the physical cube
integrals, including the low mode.

## 2. Shifted-force cap

The caps are the actual `ENNReal` suprema of the spatial `L²` slice norms on
`[0,S+1]`.  Continuity of an order-zero datum path bounds that path on the
compact interval; order-zero Parseval identifies the datum norm with the
physical `L²` norm.  If `t₀ ∈ [0,S]` and `t ∈ [0,1]`, then
`t₀+t ∈ [0,S+1]`, giving both the pointwise and iterated-supremum statements.

For `R³`, positive shifts remain in the force class by the existing restart
wiring, though B0 only needs the slice cap.  For `T³`, the module proves that
`timeShiftT t₀ f` is globally smooth and spatially periodic and satisfies the
same cap.  It does **not** claim `timeShiftT t₀ f ∈ forceClassT`: shifting a
force whose compact time support lies strictly in `(0,∞)` may make it nonzero
at the new time zero.  B3/B4 need only smoothness, periodicity, and the common
unit-window `L²` cap.

## 3. Compile-round findings

1. Opening all of `D01.Homogeneous` together with `A02` made `SpatialField`,
   `SpaceTimeField`, `IsSobolevDatum`, and `MemForceR` ambiguous.  The fix was
   to open only the four compact-component declarations and qualify the two
   datum spellings at their seam.
2. An unparenthesized `∫ x, ... + ...` let the integral binder absorb the
   following Hessian sum.  Parenthesizing the gradient and Hessian sums exposed
   the intended polynomial identity.
3. Rewriting a Schwartz coercion below `spatialPartial` did not use pointwise
   simp lemmas.  Explicit function equalities for the compact component and
   its first partial closed the H² carrier bridge.
4. The force paths are indexed at `(0 : ℕ)` coerced to `ℝ`, while the order-zero
   Parseval lemmas use literal `(0 : ℝ)`.  Explicit datum conversions with
   `Nat.cast_zero` were required on both domains.
5. The torus specializations at orders one and two similarly needed the
   natural-cast generic theorem normalized before rewriting.
6. The first probe run failed because the new modules had been checked
   directly but their `.olean` files had not yet been built:
   `object file '.../H1Bridges.olean' ... does not exist`.  Building both
   registered modules fixed that packaging issue.  The remaining probe typo
   was an unqualified `timeShiftT`; qualifying it by `Section3.T11` closed the
   probe.

## 4. File scope

New Lean files are the two formalization modules, `Targets.lean`, the closure
probe, and the axiom audit.  The only existing source/configuration files
edited are `formalization/blueprint/entrypoints.json` and the refreshed
`formalization/blueprint/AXIOM_AUDIT.json`.  No contract, binding, test,
proof-graph, guide, or registry declaration is changed.
