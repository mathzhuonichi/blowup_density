# A02 unit U1b — attempts and provenance (lane 049)

Target: the two hypotheses of
`NSFormalization.Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`
(`Source/BoundedViscosityUniqueness.lean:23`) that `ClassicalSolutionR` does not
carry as a field, on every `Icc 0 b` with `0 ≤ b < T`:

* `hB` : `∃ B, 0 ≤ B ∧ ∀ t ∈ Icc 0 b, ∀ x, ‖u.velocity (t,x)‖ ≤ B`
* `hG` : `∃ G, 0 ≤ G ∧ ∀ t ∈ Icc 0 b, ∀ x, ‖spatialDerivative u.velocity t x‖ ≤ G`
  (`spatialDerivative = NavierStokes.ProblemStatement.spatialDerivative`).

Both were proved, `sorry`-free, in
`formalization/NSFormalization/Section4/A02/Bounds.lean`
(`ClassicalSolutionR.exists_velocity_bound`, `ClassicalSolutionR.exists_gradient_bound`).

## Status of the four sub-steps at the start (COMPARISON.md U1b(i)–(iv))

* **(i) `H² ↪ L^∞` pointwise + slice extraction — EXISTED, reused verbatim.**
  - `A03.enorm_le_jetENorm` (`A03/BoundedRepresentative.lean:165`):
    `‖z x‖ₑ ≤ C · jetENorm 2 z` on `A03.SmoothL2UpTo 2`, everywhere-pointwise.
    (The registered `A03.bounded_representative`'s `supNorm_le` is bound to this
    local theorem, per `verification/Bindings/BoundedRepresentative.lean:52`.)
  - `D01.smoothSquareIntegrableJets_slice` (`D01/DatumToJets.lean:396`): the
    velocity slice of a `ClassicalSolutionR` (from `velocity_smooth` + `sobolev`)
    is smooth with all jets `L²`; `smoothJetsUpTo_of_allOrders` truncates to
    order 2 to feed `enorm_le_jetENorm`.
  - `D01.jetSobolevENorm_le_sobolevENorm` (`DatumToJets.lean:343`):
    `jetENorm m z ≤ C_m · sobolevENorm (m:ℝ) z`, so the jet `H^m` norm is bounded
    by the manuscript datum norm.
  - `D01.sobolevENorm_le_of_isSobolevDatum` (`SmoothDatum.lean:309`):
    `sobolevENorm s z ≤ ‖A‖ₑ` for any datum `A`, which turns the per-slice
    datum `G t` from `ClassicalSolutionR.sobolev` into a numeric bound.

* **(ii) the order shift for `∇u` — datum side was OPEN; proved a jet-side shift instead.**
  - The datum-side shift `‖∂ᵢu‖_{H²} ≤ ‖u‖_{H³}` on the angular carrier is
    explicitly recorded as *untouched / open* at `SmoothDatum.lean:388`.
    `D01.exists_isSobolevDatum_fderiv` (`SmoothDatum.lean:400`) gives only a
    **non-quantitative existence** of a datum for `∂_v z` (`∃ A, IsSobolevDatum s
    (∂_v z) A`), with **no** comparison `‖A‖ ≤ ‖A_z‖`. Searched
    `D01/DatumToJets.lean`, `D01/SmoothDatum.lean`, `A03/*TameProduct.lean` for
    `isSobolevDatum_partialDeriv` / `sobolevENorm_partialDeriv_le` — none exists.
  - **New lemma (this lane): the jet-side order shift** `jetENorm_dirDeriv_le`:
    `jetENorm 2 (A05.dirDeriv i w) ≤ jetENorm 3 w` for smooth `w`.
    Proof engine `norm_iteratedFDeriv_dirDeriv_le`:
    `‖iteratedFDeriv j (∂ᵢw) x‖ ≤ ‖iteratedFDeriv (j+1) w x‖`, from
    `ContinuousLinearMap.norm_iteratedFDeriv_comp_left` for the coordinate
    evaluation map `apply ℝ Space (coordinateVector i)` (operator norm `≤ 1`,
    since `‖coordinateVector i‖ = 1`) composed with `fderiv ℝ w`, and
    `norm_iteratedFDeriv_fderiv` (`‖iteratedFDeriv j (fderiv w)‖ =
    ‖iteratedFDeriv (j+1) w‖`). Then `eLpNorm_mono_enorm` lifts it to `L²`, and a
    reindex over `j ≤ 2` (`Finset.sum_range_succ'`, dropping the nonnegative
    order-0 term) gives `jetENorm 2 (∂ᵢw) ≤ jetENorm 3 w`. This is the same
    calculus as lane 019's `A05.SmoothL2.clm`, made quantitative. It **avoids**
    the open datum-side shift entirely: the gradient bound routes through
    `jetSobolevENorm_le_sobolevENorm` at order 3, not at order 2 of `∂ᵢu`.

* **(iii) `spatialDerivative u t x` = derivative of the slice — EXISTED (rfl) + reused.**
  - `spatialDerivative u.velocity t x = fderiv ℝ (fun y => u.velocity (t,y)) x`
    holds by `rfl` (definition at `NavierStokes/ProblemStatement.lean:59`), so no
    `spatialDerivative_eq_of_eqOn`/`contDiff_slice` transport is needed here.
  - `A05.opNorm_le_sum` (`A05/SmoothJets.lean`):
    `‖T‖ ≤ ∑ i, ‖T (coordinateVector i)‖`, and
    `T (coordinateVector i) = A05.dirDeriv i (slice) x` by `rfl`, reducing the
    operator-norm bound to three vector-field bounds via (i)+(ii) applied to each
    `∂ᵢ(slice)` (which is again all-jet-`L²` by
    `D01.smoothSquareIntegrableJets_dirDeriv`, `DatumToJets.lean:479`).

* **(iv) uniformity in `t ∈ Icc 0 b` — EXISTED as a pattern, reused.**
  - `IsCompact.exists_bound_of_continuousOn` applied to the `ContinuousOn G
    (Ico 0 T)` clause of `ClassicalSolutionR.sobolev` at order 2 (velocity) and
    order 3 (gradient), restricted to the compact `Icc 0 b ⊆ Ico 0 T`. Identical
    device to `A02.uniformFiniteEnergy_of_sobolevDatumPath` (`Energy.lean`, order 0).

## What was new vs reused

New (this lane, all in `Bounds.lean`): `norm_iteratedFDeriv_dirDeriv_le`,
`eLpNorm_iteratedFDeriv_dirDeriv_le`, `jetENorm_dirDeriv_le` (the jet-side order
shift, sub-step ii), the per-slice bounds `norm_le_of_datum` /
`norm_fderiv_le_of_datum`, and the two solution-class theorems.

Reused unchanged: everything in (i), (iii)-`opNorm_le_sum`, (iv)-pattern, and the
derivative-closure `smoothSquareIntegrableJets_dirDeriv`.

## Failed / rejected approaches

1. **Datum-side order shift** `sobolevENorm 2 (∂ᵢu) ≤ C · sobolevENorm 3 u`.
   Rejected: not available (open per `SmoothDatum.lean:388`); would require
   genuinely new datum-level calculus (a quantitative
   `sobolevENorm_partialDeriv_le`). The jet-side shift makes it unnecessary, so
   **no gap remains** and both bounds are proved.

2. `mul_le_mul_left'` for the `ℝ≥0∞` monotonicity steps: **not in the module's
   Mathlib import closure** (`unknownIdentifier`). Switched every such step to the
   `gcongr` tactic, which closes `a*b ≤ a*c` from the `b ≤ c` hypothesis in
   context.

3. `positivity` for `0 ≤ boundedRepresentativeConst * jetSobolevConst m`:
   would fail because those are opaque `def` constants; replaced with explicit
   `mul_nonneg (…_pos.le) (…_pos.le)`.

## Commands

- `lake build NSFormalization.Section4.A02.Bounds` → success (3.5s), no warnings
  from the new file.
- `lake env lean research/A02/axioms_u1b.lean` (scratch: applies
  `classical_uniqueness_on_Icc` with `uniformFiniteEnergy` + the two new
  theorems) → `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `#print axioms` on both theorems → `[propext, Classical.choice, Quot.sound]`.
