# T16 `lem:potential` — attempts (lane 347, Opus)

Target: `research/T16/Spec.lean` `localPotentialStatement` (`Spec.lean:328-336`)
over `CutoffData` (`:96`) and `LocalPotentialAPI` (`:145-318`), realized on the
canonical Section 3 / Section 4 vocabulary.

## What was proved (positive)

Module `formalization/NSFormalization/Section3/T16/LocalPotential.lean`:

* The 6 Spec definitions restated over canonical vocabulary (`latticeVector`,
  `periodicSet`, `periodicScaledPacket`, `correctedBackground`, `CutoffData`,
  `LocalPotentialAPI`) plus `localPotentialStatement`.  The probe
  `research/T16/probes/api_on_canonical.lean` proves each helper `def` equals the
  Spec's (which uses the `Contracts.V1` copies) by `rfl`, and converts both
  structures fieldwise both directions (`CutoffData` by the structure exception
  with `rfl` roundtrips; `LocalPotentialAPI` by defeq of all 26 fields), so
  `Contracts.V1.{curl,cross,scaledSpatialCutoff,scaledTemporalCutoff,scaledPacket,
  spatialDivergence}` are confirmed definitionally the canonical notions.
* `exists_originCutoff` — spatial Urysohn cutoff at the origin with smoothness,
  compact support, open plateau ⊇ K, `θ = 1` on the plateau, support radius,
  support ⊆ `ball 0 R`, **and** the `[0,1]` range (strengthens I02
  `exists_prescribed_cutoff`, which drops the range).
* `exists_timeCutoff` — temporal Urysohn cutoff with `[0,1]` range, `η = 1` on
  `[-1,1]`, support ⊆ `(-2,2)`.
* `exists_threshold` — `ε₀ > 0` with `2ε² < min T δ` and `ε·θRadius < r` for all
  `ε ∈ (0,ε₀]` (witness `ε₀ = min 1 (min (min T δ/3) (r/(θRadius+1)))`).
* `localPotential_zero` — the **full** `LocalPotentialAPI` for the reference
  `v = 0` (with the actual cutoffs/threshold and zero potential/correction);
  discharges every one of the 26 fields.  Transported to the Spec's structure in
  the probe as the non-vacuity `v = 0, U = 0, K = {0}` example.
* `specStatement_of_module : localPotentialStatement (module) → localPotentialStatement (Spec)`
  in the probe: the module's general theorem, once proved, closes the Spec's.

All declarations print exactly `[propext, Classical.choice, Quot.sound]`
(`research/T16/axioms_local_potential.lean`).

## Gap 1 — the radial potential on the ball (spatial locality of `v`)

`potential_smooth` and `potential_curl` are stated on the coordinate ball
`Ioo 0 (T+δ) ×ˢ Metric.ball x₀ r`, and the T16 hypothesis gives `v` smooth /
divergence-free **only there**.  The Section 4 I02 lemmas the brief points at
require `v` smooth on all of physical space in the slab.  Attempting

```lean
exact spatialCurl_timePotential_on hv (…) x₀ ht x
```

with `hv : ContDiffOn ℝ ∞ v (Ioo 0 (T+δ) ×ˢ Metric.ball x₀ r)` fails:

```
error: Application type mismatch: The argument
  hv
has type
  ContDiffOn ℝ ∞ v (Ioo 0 (T + δ) ×ˢ Metric.ball x₀ r)
but is expected to have type
  ContDiffOn ℝ ∞ v (Ioo 0 (T + δ) ×ˢ univ)
```

`I02.timePotential_contDiffOn` and `I02.spatialCurl_timePotential_on` both take
`ContDiffOn ℝ ∞ v (I ×ˢ (univ : Set Space))` (see `Reference.lean:86,102`), and
`spatialCurl_timePotential_on` also needs `hdiv` on all `x : Space`.  So these are
**not reusable verbatim** for the local (ball-only) hypotheses of T16.

Residual lemmas that must be delivered (a spatial analogue of I02
`Reference.lean`'s time truncation — not in the tree):

```lean
-- Spatial companion of I02.timePotential_contDiffOn.
theorem timePotential_contDiffOn_ball {v : VelocityField} {x₀ : Space} {r : ℝ}
    {I : Set ℝ} (hI : IsOpen I)
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r)) :
    ContDiffOn ℝ ∞ (RadialPotential.timePotential v x₀) (I ×ˢ Metric.ball x₀ r)

-- Spatial companion of I02.spatialCurl_timePotential_on.
theorem spatialCurl_timePotential_on_ball {v : VelocityField} {x₀ : Space} {r : ℝ}
    {I : Set ℝ} (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ I, ∀ x ∈ Metric.ball x₀ r, spatialDivergence v t x = 0)
    {t : ℝ} (ht : t ∈ I) {x : Space} (hx : x ∈ Metric.ball x₀ r) :
    SpatialCurl.curl (fun y => RadialPotential.timePotential v x₀ (t, y)) x = v (t, x)
```

Proof route (not attempted to completion this lane): for `x ∈ ball x₀ r` the
radial segment `{x₀ + ρ•(x-x₀) : ρ ∈ [0,1]}` is a compact subset of the open
`ball x₀ r`; multiply `v` by a spatial bump equal to one on a neighborhood of
that segment and supported in `ball x₀ r` to obtain a globally smooth `V` with
`V = v` on the used set; apply the global I02 lemmas to `V`; transfer through
`I02.timePotential_congr_slice`.  `potential_formula` itself is definitional
(`RadialPotential.centeredPotential_eq_integral`, `rfl`).

## Gap 2 — the periodic correction (the lattice lift)

The Spec forces `D.correction ε` to be **unit-periodic** (`correction_periodic :
IsPeriodicOn univ`) with slice support in `periodicSet (ball x₀ r)`
(`correction_support_ball`).  A compactly supported `R³` field is not periodic, so
`D.correction ε` must be the periodic lift of the chart correction
`physicalCorrection v x₀ T θ η ε`:

```lean
correction ε (t,x) = ∑' k : PeriodicFrequency,
  physicalCorrection v x₀ T θ η ε (t, x - latticeVector k)
```

Open sub-lemmas (none in the tree; flagged in `COMPARISON.md`
“Exact T10 lemmas needed”):

* local finiteness: with `ε·θRadius < r < 1/2` the translated supports
  `ball (x₀ + latticeVector k) (ε·θRadius)` are pairwise disjoint and locally
  finite;
* `correction_smooth`: `ContDiff ℝ ∞` of the locally-finite lattice sum;
* `correction_periodic`: `IsPeriodicOn univ` of the lift — needs the T10
  physical-bridge lemma `IsPeriodicOn I z → ∀ t ∈ I, ∀ x, ∀ k, z (t, x +
  latticeVector k) = z (t, x)` and the `periodicSet` unit-shift invariance
  `x ∈ periodicSet S ↔ x + coordinateVector i ∈ periodicSet S`;
* `correction_support` / `correction_support_ball`: support of the lift;
* `correction_divergence_free`: divergence of the lift is zero (locally one
  translate of a curl; `NSFormalization.Paper1.localCorrection_divergence` gives
  the single-chart fact);
* `correction_formula`: on `ball x₀ r` the lift is the `k = 0` term
  (`tsum_eq_single 0` from disjointness), i.e. the chart curl formula;
* `correction_cancels` (`eq:bgzero`): on `Ico (T-ε²) T`, `η_ε = 1`
  (`eta_one`) and on the scaled plateau `θ_ε = 1` with vanishing derivatives
  (`theta_one`), so `physicalCorrection = -∇×A = -v`
  (`NSFormalization.Paper1.localCorrection_eq_neg`) on an open neighborhood of
  the packet support, giving `v + w_ε = 0` there.

## Negative notes

* Tried to discharge `potential_curl`/`potential_smooth` from the I02 lemmas
  directly — blocked by the `univ` vs `ball x₀ r` mismatch above.  Do not report
  these fields as closed for general `v`.
* Did not attempt a `sorry`/`axiom`/`def _ : Prop := <goal>` stub for any open
  field; the honest partial (cutoffs + threshold + defeq probe + `v = 0`
  instance) is delivered instead.
