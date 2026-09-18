# T16 Gap 1 (lane 351, Opus) — the radial potential on the chart ball

Target: the two residual lemmas of `research/T16/ATTEMPTS.md` §"Gap 1", verbatim,
and the three T16 potential fields packaged for lane 353.
Module: `formalization/NSFormalization/Section3/T16/BallPotential.lean`.

## What was proved (positive)

* `timePotential_contDiffOn_ball {v x₀ r I} (hI : IsOpen I)
  (hv : ContDiffOn ℝ ∞ v (I ×ˢ ball x₀ r)) :
  ContDiffOn ℝ ∞ (timePotential v x₀) (I ×ˢ ball x₀ r)` — Gap 1a, verbatim.
* `spatialCurl_timePotential_on_ball {v x₀ r I}
  (hv : ContDiffOn ℝ ∞ v (I ×ˢ ball x₀ r))
  (hdiv : ∀ t ∈ I, ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0)
  {t} (ht : t ∈ I) {x} (hx : x ∈ ball x₀ r) :
  SpatialCurl.curl (fun y => timePotential v x₀ (t, y)) x = v (t, x)` — Gap 1b,
  verbatim.  **`I` open is NOT needed here** (the spatial slice is extracted from
  `hv` by `ContDiffOn.comp` at the fixed time `t`); the statement is exactly the
  ATTEMPTS.md one, no extra `hI`.
* `exists_potential_on_ball` — the three T16 fields `potential_smooth`,
  `potential_formula`, `potential_curl` (canonical
  `NSFormalization.Section3.T16.LocalPotentialAPI` spellings) with witness
  `A := timePotential v x₀`.
* Supporting new lemmas: `curl_potential_of_segment`,
  `curl_centeredPotential_of_segment` (segment-localized weakenings of
  `RadialPotential.curl_potential` / `curl_centeredPotential`),
  `timePotential_congr_segment` (slicewise segment congruence),
  `contDiffOn_bumpSmul`, `contDiff_bumpSmul_slice` (smoothness of `χ·v`).

All 8 declarations print `[propext, Classical.choice, Quot.sound]`
(`research/T16/axioms_ball_potential.lean`).

## Route decisions (recording the branch points of ATTEMPTS.md §Gap1)

* **Smoothness (Gap 1a).** Reused `I02.timePotential_contDiffOn` (it already does
  the time-truncation via `exists_local_truncation`) rather than re-running the
  truncation.  The truncated field `V₁ = χ·v` is `ContDiffOn ℝ ∞` on `I ×ˢ univ`
  (proved casewise in `contDiffOn_bumpSmul`: on the ball `v` is `ContDiffAt`; off
  `tsupport χ` the product is locally `0`; the two cases cover `univ` because
  `tsupport χ ⊆ closedBall x₀ r'' ⊆ ball x₀ r`).  A single global bump cannot
  cover the *whole* open ball (its plateau would have to be all of `ball x₀ r`,
  forcing `tsupport χ ⊄ ball x₀ r`), so the argument is per-point:
  `ContDiffWithinAt` at each `z`, with the bump plateau `ball x₀ r'`,
  `dist z.2 x₀ < r' < r` chosen for that `z`.
* **Curl (Gap 1b) — is `spatialCurl_timePotential_on` global? YES.**  It calls
  `RadialPotential.curl_centeredPotential hs (hdiv t ht) x₀ x` whose `hdiv`
  argument is `∀ x, … = 0` (all of space).  So it is **not** reusable for
  ball-only `hdiv`.  Re-derived locally (option b): reading `curl_potential`, the
  divergence enters only as `hdiv (r • x)` for `r` in the integration interval
  `[0,1]`; replacing its `funext` step by `intervalIntegral.integral_congr` on
  `[[0,1]] = Icc 0 1` gives `curl_potential_of_segment`, needing `hdiv` only on
  the segment.  `χ·v` is divergence-free on the plateau ball `ball x₀ r'` (there
  `χ ≡ 1`, so `div(χv) = ∇χ·v + χ·div v = 0 + 1·0`), which contains the segment,
  so it qualifies; the curl of the slice is transferred by `fderiv` congruence
  (`Filter.EventuallyEq.fderiv_eq`) on the open plateau ball.

## Negative notes / dead ends considered

* **Cannot** apply `I02.timePotential_contDiffOn` / `spatialCurl_timePotential_on`
  directly to `v` — type error `ContDiffOn … (I ×ˢ ball x₀ r)` vs expected
  `(I ×ˢ univ)` (recorded in `ATTEMPTS.md` §Gap1).  Confirmed by re-reading the
  I02 sources: both take `ContDiffOn ℝ ∞ v (I ×ˢ univ)`.
* **Cannot** replace `χ·v` by a globally divergence-free extension of `v`: a
  compactly-cut field `χ·v` is not divergence-free on the annulus where `χ`
  varies, and a genuine solenoidal global extension is not available in the tree.
  The segment-localized curl lemma sidesteps this — divergence-freeness is only
  needed on the segment, where `χ·v = v`.
* **Not attempted:** Gap 2 (the periodic lattice lift of the correction) — out of
  scope for this lane; unchanged from `ATTEMPTS.md` §Gap 2.
* No `sorry`/`axiom`/`native_decide`/goal-repackaging: every lemma has a genuine
  analytic hypothesis strictly weaker than (or orthogonal to) its conclusion.
  `set_option maxHeartbeats 400000` (≤ policy cap 400000) is used on the two main
  transfer lemmas only, each commented.
