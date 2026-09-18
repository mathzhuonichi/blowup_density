# T16 `lem:potential` — spec / reconciliation observations (lane 347)

The Spec is **not** changed (per lane rules).  These are notes for the owner.

## 1. “Reusable verbatim” overstates the I02 reuse (spatial locality)

`RECONCILIATION.md` and the lane brief state that the Section 4 I02 proof of the
same lemma (`timePotential_contDiffOn`, `spatialCurl_timePotential_on`,
`exists_prescribed_cutoff`) is “reusable verbatim for the local part”.  This is
accurate for the **cutoffs** (`exists_prescribed_cutoff`, up to the `[0,1]`
range clause that `exists_originCutoff` re-adds) but **not** for the potential:

* `I02.timePotential_contDiffOn` (`Reference.lean:86`) and
  `I02.spatialCurl_timePotential_on` (`Reference.lean:102`) both require
  `ContDiffOn ℝ ∞ v (I ×ˢ (univ : Set Space))` — `v` smooth on **all** of
  physical space in the time slab — and the curl lemma additionally requires
  `hdiv` at every `x : Space`.
* `Spec.localPotentialStatement` (`Spec.lean:333-335`) gives `v` smooth and
  divergence-free **only** on `Ioo 0 (T+δ) ×ˢ Metric.ball x₀ r`.

Passing the ball-only hypothesis to the I02 lemma is a hard type error (exact
text in `ATTEMPTS.md`, Gap 1).  Bridging requires a *spatial* truncation lemma
(the spatial analogue of the time truncation in I02 `Reference.lean`), which is
new mathematics not present in `formalization/` or `vendor/`.

Root cause: the manuscript (`03-torus.tex:164`) fixes the reference `(v,π,g)`
*globally* smooth on `[0,T+δ]` (i.e. on the whole torus), whereas the reconciled
Spec localized the smoothness/divergence hypotheses to the coordinate ball.  The
localized form is defensible (the potential only reads `v` inside the ball) but
it forfeits the direct I02 reuse.  Owner decision: either

* register the missing spatial-truncation lemmas as an explicit T16 prerequisite
  (recommended; keeps the localized Spec), or
* strengthen the Spec hypothesis to `ContDiffOn ℝ ∞ v (Ioo 0 (T+δ) ×ˢ univ)` and
  divergence-free on all `x`, matching the manuscript’s global reference, after
  which `potential_smooth`/`potential_curl` follow from I02 verbatim.

## 2. `correction_periodic` forces a lattice lift, not a plain zero-extension

The proof sketch (`03-torus.tex:187-188`) says “extending by zero gives a
globally smooth periodic field”.  In the Spec that is encoded as
`IsPeriodicOn univ (D.correction ε)` together with slice support in
`periodicSet (ball x₀ r)`, which requires `D.correction ε` to be the **periodic
lift** `∑' k, physicalCorrection(·, · - latticeVector k)`, not the compactly
supported chart correction.  Every `correction_*` field is therefore coupled to
the lift; the two elementary lattice lemmas needed
(`IsPeriodicOn`→integer-translate invariance, and `periodicSet` unit-shift
invariance) are exactly the two flagged in `COMPARISON.md`’s “Exact T10 lemmas
needed”, and are not yet registered by the T10 physical-bridge lane.  No Spec
change is implied; this only records the size of the remaining obligation.
