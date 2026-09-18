# Lane 351 — T16 gap 1: the radial vector potential on the chart ball (Opus prover; report transcribed by the lead from the agent's final message, since the report-file guard blocked the agent's own write)

Commit `88768071c0e7cc66f33498108773300b449a2e34` on `erenup/351-T16-ball-potential` (stacked on lane 347).

## 1. What was proved
Gap 1 of `research/T16/ATTEMPTS.md` is closed for general local `v`: the radial vector potential is `C^∞` and its spatial curl recovers `v` on `I ×ˢ Metric.ball x₀ r`, where `v` is only smooth / divergence-free on that ball (the Section 4 I02 lemmas need `I ×ˢ univ`). Module `NSFormalization.Section3.T16.BallPotential`:

```lean
theorem timePotential_contDiffOn_ball {v : VelocityField} {x₀ : Space} {r : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r)) :
    ContDiffOn ℝ ∞ (timePotential v x₀) (I ×ˢ Metric.ball x₀ r)

theorem spatialCurl_timePotential_on_ball {v : VelocityField} {x₀ : Space} {r : ℝ} {I : Set ℝ}
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ I, ∀ x ∈ Metric.ball x₀ r, spatialDivergence v t x = 0)
    {t : ℝ} (ht : t ∈ I) {x : Space} (hx : x ∈ Metric.ball x₀ r) :
    SpatialCurl.curl (fun y => timePotential v x₀ (t, y)) x = v (t, x)

theorem exists_potential_on_ball {v : SpaceTimeField} {x₀ : Space} {r T δ : ℝ}
    (hv : ContDiffOn ℝ ∞ v (Ioo (0:ℝ) (T + δ) ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0:ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r, spatialDivergence v t x = 0) :
    ∃ A : SpaceTimeField,
      ContDiffOn ℝ ∞ A (Ioo (0:ℝ) (T + δ) ×ˢ Metric.ball x₀ r) ∧
      (∀ t x, A (t, x) = ∫ ρ in (0:ℝ)..1, ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)) ∧
      (∀ t ∈ Ioo (0:ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
        SpatialCurl.curl (fun y => A (t, y)) x = v (t, x))
```
The second lemma needs no `IsOpen I` (the fixed-time slice is pulled from `hv` by `ContDiffOn.comp`). The three conjuncts are the field types of `potential_smooth` / `potential_formula` / `potential_curl` with `D.potential := timePotential v x₀`.

Supporting lemmas: `curl_potential_of_segment`, `curl_centeredPotential_of_segment` (divergence-freeness needed only on the radial segment `[x₀, x]`), `timePotential_congr_segment`, `contDiffOn_bumpSmul`, `contDiff_bumpSmul_slice`. Route (option (b) of ATTEMPTS §Gap 1): I02's `spatialCurl_timePotential_on` is genuinely global (`hdiv : ∀ x`), so the curl identity was re-derived locally; the bump-truncated `χ·v` is divergence-free on the plateau ball containing the segment.

## 2. Files
`formalization/NSFormalization/Section3/T16/BallPotential.lean`; probe `research/T16/probes/ball_potential_closes.lean` (three canonical field types via the `D.potential` projection + nonzero constant-field non-vacuity instance); `research/T16/axioms_ball_potential.lean` (8 declarations, all `[propext, Classical.choice, Quot.sound]`); `research/T16/ATTEMPTS_BALL_POTENTIAL.md`; status line in `research/T16/COMPARISON.md`.

## 3. Gaps
Gap 2 (the periodic lattice lift, all `correction_*` fields) untouched — lane 352. No residual goal in this lane. `set_option maxHeartbeats 400000 in` (policy cap) on the two transfer lemmas, commented; it must precede the docstring.

## 4. Commands and results
`lake build NSFormalization.Section3.T16.BallPotential` → success (9358 jobs); `lake env lean` on the module / probe → no output; on the axioms file → 8 × `[propext, Classical.choice, Quot.sound]`; `make check` → OK.
