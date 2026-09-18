# T16 gap 2 — the lattice lift (lane 352, Opus)

Target: the seven `correction_*` fields of the canonical `LocalPotentialAPI`
(`formalization/NSFormalization/Section3/T16/LocalPotential.lean`), realized as
lemmas about the unit-periodic lift of a compactly supported chart correction.

Result: **all seven closed**, module `Section3/T16/LatticeLift.lean`, green build,
`[propext, Classical.choice, Quot.sound]` on every declaration.

## Key decision: reuse OpenAI's periodization verbatim

`latticeLift w := fun z => ∑' k : PeriodicFrequency, w (z.1, z.2 - latticeVector k)`
is **definitionally** `NavierStokes.PeriodicLocalization.periodize w`:
`latticeVector k = lattice k` holds by `rfl` (both are
`WithLp.toLp 2 (fun i => (k i : ℝ))`; `WithLp.equiv_symm_apply` is `rfl`), and the
index types `PeriodicFrequency`/`Lattice` are both `Fin 3 → ℤ`.  Hence
`latticeLift_eq_periodize : latticeLift w = periodize w := rfl`, and the whole
local-finiteness / smoothness / periodicity infrastructure of `PeriodicLocalization`
is reused with no re-proof.  (T13 `Localization.lean` has a `periodize` too, but
only for `SpatialField`; the spacetime one used here is the upstream `NavierStokes`
module — the correct object for `SpaceTime → Space` chart corrections.)

## Per-field transport

* `latticeLift_smooth` ← `contDiff_periodize` (needs `SupportedInCube`, derived
  from ball slice support by `supportedInCube_of_ball`).
* `latticeLift_periodic` ← `unitSpatialPeriodsOn_periodize`
  (`IsPeriodicOn univ` is textually `UnitSpatialPeriodsOn univ`).
* `latticeLift_eq_of_ball` (the analytic core of `correction_formula`,
  `correction_cancels`): on `ball x₀ r` with `r + ρ ≤ 1` and slice support in
  `ball x₀ ρ`, `tsum_eq_single 0` collapses the sum to the `k = 0` term, because
  for `k ≠ 0` and `x ∈ ball x₀ r` the coordinate estimate
  `|k i| ≤ |x i - x₀ i| + |x i - k i - x₀ i| < r + ρ ≤ 1` forces `k = 0`.
* `latticeLift_divergence_zero`: local finite sum (`periodize_locally_eq_sum`) +
  `sdiv_congr` (spatial-slice `EventuallyEq` transports the divergence) +
  `spatialDivergence_finsetSum` (Finset induction on `spatialDivergence_add`) +
  `spatialDivergence_translate` (translation shifts the derivative's base point,
  via `HasFDerivAt.comp` with `fderiv (· - c) = id`).
* `latticeLift_timeSupport` (`correction_support`): `HasCompactSupport w` makes
  `Prod.fst '' tsupport w` closed; `support (periodize w) ⊆ (Prod.fst '' tsupport w)
  ×ˢ univ`; hence `tsupport ⊆` that closed set `⊆ Ioo … ×ˢ univ`.
* `latticeLift_sliceSupport` (`correction_support_ball`): per point `x ∉
  periodicSet (ball x₀ r)`, the local finite sum shows the slice is `=ᶠ 0` (each
  translate's tsupport ⊆ `closedBall (x₀ + lattice n) ρ`, disjoint from `x` since
  `ρ < r`), so `x ∉ tsupport`; combine the finitely many translates with
  `eventually_all_finset`.
* `latticeLift_cancels` (`correction_cancels`): choose `O = periodicSet (ball x₀ r)`
  (open, a union of ball preimages).  Both `v` and `latticeLift w` are
  unit-periodic, so `isPeriodicOn_sub_latticeVector` (OpenAI's
  `periodic_integerShift`) reduces any `x ∈ periodicSet (ball x₀ r)` to
  `x - latticeVector k ∈ ball x₀ r`, where `latticeLift w = w` and the chart
  cancellation `v + w = 0` holds.

## Packaging

`correction_fields_of_chart` takes the scale-indexed chart family `W` and its
transportable per-`ε` chart facts (smooth, compact support, divergence-free, the
product support bound `Ioo … ×ˢ ball x₀ (ε·θRadius)`, the chart curl formula, the
chart cancellation on `ball x₀ r`, the T14 packet support bound) and returns the
seven canonical field bodies for `fun ε => latticeLift (W ε)`, so lane 353 fills
`LocalPotentialAPI.correction` by projection.  The two support facts (slice /
spacetime) and `r + ε·θRadius ≤ 1` are derived once from `hWtsupp` + `hεspace`.

## Negative notes / dead ends

* `MixedPeriodicAssembly.periodize_divergence_free` exists but is tied to
  `SupportedInCube (1/4)` (support in the cube at the **origin**) via the
  `representative`/`nearestIndex` fundamental-cube reduction; the T16 ball is
  centred at an arbitrary `x₀`, so that lemma is not reusable.  Divergence-free
  was instead proved for arbitrary `x₀` via the finite-sum route above.
* `fderiv_comp` with `differentiableAt_id.sub_const` produced a `fun y => id y - c`
  form that would not `rw`-match the `fun y => y - c` composition; replaced with
  `HasFDerivAt.comp` + `.fderiv` + `ContinuousLinearMap.comp_id`.
* Coordinate-of-finite-sum `(∑ vₙ) i = ∑ (vₙ i)` has no direct EuclideanSpace
  lemma (`exact?` fails, `PiLp.sum_apply` does not exist); avoided by proving
  `spatialDivergence_finsetSum` by induction on `spatialDivergence_add`
  (`PiLp.add_apply` does exist), never extracting a coordinate of a sum.
* Names: `abs_add` → `abs_add_le`; `ContinuousLinearMap.add_apply` → `add_apply`.

## Not this lane (Gap 1, still open)

`potential_smooth` / `potential_curl` for general local `v` (the ball-vs-univ
mismatch of the I02 lemmas) is a separate residual, documented in `ATTEMPTS.md`
§Gap 1; untouched here.
