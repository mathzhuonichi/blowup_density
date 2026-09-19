# T17 U11 (`eq:HHs`, `L¹_tH^s_x`) — attempts ledger, lane 438

Target: `sobolevConst`, `sobolevConst_pos`, `forceSobolev_memLp`,
`force_sobolev_bound` of the canonical `CorrectionAPI`
(`Section3/T17/Correction.lean:262-282`) at the concrete `correctionData`
of unit U2, for `0 ≤ s ≤ 1`.

## What worked (the delivered route)

Not the brief's route.  The delivered proof goes through Paper1's **periodic
Fourier-series** machinery, not through the registered T13 `localization`
Gagliardo inequality.  Chain, per admissible `ε`:

1. `Transport.force_eq` (U2) — the torus force is `latticeLift G` with
   `G = Source.correctionForce ν v (physicalCorrection …)` the single Euclidean
   copy, and `latticeLift = NavierStokes.PeriodicLocalization.periodize` by `rfl`
   (`T16.latticeLift_eq_periodize`).
2. New `shiftedForce` — the same copy recentred at the spatial origin.  Paper1's
   periodization estimates measure support in the **origin-centred** cube
   `SupportedInCube r` (`|z i| ≤ r`, `r < 1/2`), while the chart ball of
   `PlacementData` sits inside `(0,1)³`; recentring reconciles the two
   normalizations without any new hypothesis on `‖x₀‖`.
3. `Section3/T11/Transport.isPeriodicDatum_translate` +
   `translatePeriodicDatum_norm` give translation invariance of T10's
   `periodicSobolevENorm`, so the recentring costs nothing.
4. New `norm_scalar_datum_real` / `norm_datum_eq_sqrt` — the T10 order-`s` datum
   norm **is** Paper1's `periodicVectorSobolevNorm` at every *real* order, via
   `Paper1.norm_smoothPeriodicWeightedFourierLp`.  (`T10.norm_scalar_datum_nat`
   only covers natural orders because it converts to `periodicIntegerEnergy`;
   stopping one rewrite earlier gives every real order.)
5. `Paper1.PeriodicForceEndpointScaling.periodized_scalar_L1Hs_le_endpoint_product`
   — the periodized scalar `L¹_tH^s` norm is bounded by the endpoint product
   `‖·‖_{L¹H⁰}^{1-s} · (2π‖·‖_{L¹H¹})^s` for `0 ≤ s ≤ 1`.
6. `Source.fourierSobolevNorm_translate` undoes the recentring on the whole-space
   endpoint norms, and
   `Paper1.PeriodicCorrectionEndpointRates.correction_scalar_whole_endpoint_rates`
   supplies `‖·‖_{L¹H⁰} ≤ C₀ ε^{3/2}`, `‖·‖_{L¹H¹} ≤ C₁ ε^{1/2}`.
   `(ε^{3/2})^{1-s}(ε^{1/2})^s = ε^{3/2-s}` is the delivered rate.
7. The honest path: new `force_coefficient_path_real`, the order-`s` analogue of
   `T10.force_coefficient_path`.  Continuity of the datum path at fractional `s`
   is *not* available from `T10.continuous_datum_path` (natural orders only); it
   follows by squeezing against the order-`1` path through the new
   `norm_datum_mono`, itself `Paper1.periodicSobolevSq_mono_smooth`.

Delivered constant:
`sobolevConst … s = 1 + ∑_{i<3} c₀(i)^{1-s} · (2π c₁(i))^s`, with `c₀ c₁` the
`toReal` of Paper1's two endpoint profile constants (`Classical.choose`, the
house style of lane 385's `forceDerivConst`).  It is `ε`-independent and
positive on the whole range because of the `1 +`.  The proof actually gives
`≤ ofReal(ε^{3/2-s}·K)`; the manuscript's `ε^{3/2} + ε^{3/2-s}` is then reached
by the trivial majorization, which is why `+1` is harmless.

## What was tried and abandoned

1. **The brief's route (T13 `localization` + D01 `dotHomogeneousENorm`).**
   `T13.Assembly.localization` is proved and its ball hypothesis
   `closure (ball x₀ r) ⊆ interior fundamentalCube` is derivable from
   `CorrectionAPI.ball_in_chart` + `PlacementData.chartBall_in_cube`, so the
   route is not blocked geometrically.  It is blocked *quantitatively*: its RHS
   is `eLpNorm f 2 volume + dotHomogeneousENorm s f`, and
   `dotHomogeneousENorm` (`Section4/D01/HomogeneousNorm.lean:26`) is the
   datum infimum whose value is `homogeneousFourierENorm`
   (`D01.isHomogeneousSliceDatum_compact`), i.e. an integral against
   `Source.angularFourier` (the `e^{-i x·ξ}` convention).  Paper1's ε-rates
   (`correction_scalar_whole_endpoint_rates`) are stated with Mathlib's `𝓕`
   (`e^{-2πi x·ξ}`).  Bridging them needs a `(2π)^{3+2s}` change of variables in
   an `ℝ≥0∞` lintegral over `Space`; `grep -rn "angularFourier" formalization/`
   shows no such whole-space Plancherel/dilation bridge in the tree (only the
   scalar `PeriodicScalarForceEndpoints.angularSobolevSq_{zero,one}_eq_physical`
   for the two integer endpoints).  Building it would be a lane of its own, and
   the resulting bound is the same one Paper1 already proves.  Recorded as the
   residual for a later lane that wants `eq:HHs` proved *through* `lem:localization`
   rather than through the periodic Fourier series.
2. **Monotone-in-order bound** `‖·‖_{H^s} ≤ ‖·‖_{H^1}` for `s ≤ 1`.  Provable
   (it is `norm_datum_mono`) but gives the rate `ε^{1/2}`, which is *weaker*
   than `ε^{3/2-s}` for `ε < 1`, `s < 1`.  Kept only as the continuity tool.
3. **Using `Paper1.PeriodicCorrectionEndpointInstantiation.eventually_correction_coordinate_periodized_endpoint_product:30`
   directly** (the only pre-existing *periodized* endpoint statement for this
   force).  Rejected: it is an `∀ᶠ ε in 𝓝[>] 0` statement and carries
   `hcenter : ‖x₀‖ < 1/4`.  The field needs every `ε ∈ (0, D.ε₀]`, and `‖x₀‖`
   is not small for a chart ball inside `(0,1)³`.  Its own proof
   (`periodized_scalar_L1Hs_le_endpoint_product` + the rates) is what this lane
   reuses, applied to the recentred copy so that no `‖x₀‖` hypothesis is needed.
4. **`abel` on `z.2 - lattice n + x₀ = z.2 + x₀ - lattice n`** in
   `periodize_shiftedForce`: leaves the goal
   `z.2 + -1 • lattice n + x₀ = -1 • lattice n + (z.2 + x₀)` unsolved on
   `EuclideanSpace ℝ (Fin 3)` (`PiLp`).  `sub_add_eq_add_sub` closes it directly.
5. **`mul_le_mul_left'`** — unknown identifier at this pin; used
   `mul_le_mul' le_rfl h` instead.
6. `rw [fourierSobolevNorm_translate]` fails after a `funext`-produced
   beta-redex `fun x => (fun y => …) (x - -x₀)`; applying the lemma with `exact`
   after `simp only [sub_neg_eq_add]` works.

## Premises

Same block as lanes 385/425, i.e. `hv : ContDiff ℝ ∞ v` (the documented G1 of
`SPEC_ISSUES.md`) plus the geometric/cutoff data, `hr2 : r < 1/2`, and
`hε₀ : ε₀ ≤ 1` (lane 385's `force_derivative_bound` already carries it; at
assembly it comes from `eps_le_placement` and `PlacementData.eps_le_one`).
No named input, no placeholder, no new `Prop` field.

`hv` is used three times: Paper1's `correction_scalar_whole_endpoint_rates`
and `physicalForce_smooth` need global smoothness of the reference, and
`force_eq` (through `U7.force_smooth`/`force_periodic`/`force_support`) needs it
on the chart cylinder.

## Mutation probes (run from `/tmp/u11mut`, not committed)

* `ε^{3/2-s}` → `ε^{3/2+s}`: `error: Type mismatch … ε ^ (3 / 2 - s) … but is
  expected to have type … ε ^ (3 / 2 + s)`.
* `s ≤ 1` → `s ≤ 2` on all three fields: three `Type mismatch` errors printing
  the delivered `s ≤ 1` range.


> Lead correction after review 438: the "no angularFourier/Mathlib-Fourier bridge; only endpoints" sentences are withdrawn — the arbitrary-real convention equivalence exists in `Source/FourierConvention.lean:23-143` and `Source/AngularForceNorms.lean:19-50`; only a direct `ENNReal` adapter from `dotHomogeneousENorm` to the Paper1 norm (needed by the T13-localization route) was not found.
