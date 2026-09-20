# T15 U-TB1 — attempts, dead-ends, and design record (lane 364)

Target: the energy Haar/Lebesgue single-copy bridges for `periodize f`
(`research/T15/T15_SPLIT.md` unit U-TB1). Shipped module:
`formalization/NSFormalization/Section3/T15/HaarBridge.lean`.

## What worked (final design)

The whole unit rests on one observation that the brief's suggested route
(Bochner `integral_torusLift` + `ofReal_integral_eq_lintegral_ofReal` +
`lintegral_fundamentalCube_ofReal`, which all need continuity/integrability)
does **not** exploit:

- Mathlib already proves `UnitAddTorus.lintegral_preimage`
  (`Mathlib/Analysis/Fourier/AddCircleMulti.lean:186`): Haar `lintegral` on the
  torus unfolds to a Lebesgue `lintegral` over the `Ioc`-box, **for any**
  `ℝ≥0∞`-valued integrand. Composing it with the volume-preserving chart
  `toSpace` (via `T13.TorusIdentity.toSpace_preimage_fundamentalCube` and
  `MeasurePreserving.setLIntegral_comp_preimage_emb`) and `Paper1.torusLift_coe`
  gives `lintegral_enorm_torusLift`, hence `eLpNorm_torusLift_restrict`, with
  **zero regularity or measurability hypotheses on `g`**. This is strictly
  stronger than the brief's route and made both the energy and the gradient
  companion fall out without needing `periodize f` to be smooth.

- Goal 1 = bridge ∘ `eLpNorm_periodize_restrict_eq` (single copy `periodize f = f`
  on the closed cube). Goal 3 = Goal 1 at a slice. Goal 2 = bridge ∘ (a.e.
  `∇periodize f = ∇f` on the cube, null frontier) ∘ (`gradientENorm` identity for
  the smooth `f`) ∘ (support restriction).

## Dead-ends / rejected routes

1. **Brief's Bochner route for the bridge (rejected as unnecessary and weaker).**
   `∫⁻ ofReal (torusLift G) = ofReal (∫ torusLift G) = ofReal (cubeIntegral G)`
   needs `Integrable (torusLift G)` and `Continuous G` (for
   `lintegral_fundamentalCube_ofReal`). Replicating `Paper1.memLp_torusLift` for
   a real `G` is extra work, and it would have forced a continuity hypothesis on
   every consumer. `UnitAddTorus.lintegral_preimage` avoids all of it. Kept the
   brief's cited lemmas only where genuinely needed (`toSpace_preimage_*`).

2. **Gradient via `periodize f` smoothness (rejected — dependency on lane 365 U1).**
   The clean chain would be bridge → `gradientENorm (periodize f) (restrict cube)`
   → `T13.endpoint_one_eq`. But identifying `eLpNorm (∇(periodize f))` with
   `gradientENorm (periodize f)` needs `fderiv (periodize f)` measurable, i.e.
   `periodize f ∈ C¹`, which is exactly `contDiff_periodize` — available only
   through the lane-352/U1 `rfl` bridge to the vendor `periodize`, **not landed**.
   Avoided entirely: replace `∇(periodize f)` a.e.-on-the-cube by `∇f` (they
   agree on `interior fundamentalCube` by `periodize_eventuallyEq_interior`, and
   the cube minus interior is `volume_frontier_fundamentalCube`-null), then use
   the `gradientENorm` identity for the genuinely smooth `f`. No `periodize`
   regularity used anywhere in the module.

3. **`rw [torusLift_coe ...]` inside the `setLIntegral_congr_fun` congruence
   (failed, fixed).** `torusLift_coe` is stated for `Paper1.torusLift`; the goal
   carries the defeq T10 abbrev `torusLift`, so `rw` could not find the pattern
   `Paper1.torusLift g (fun i => ↑(y i))`. Replaced by
   `congrArg (fun a => ‖a‖ₑ ^ q) (torusLift_coe ...)`, which closes the goal up
   to defeq via `exact`.

4. **Ball vs interior hypothesis.** The T13 endpoint lemmas
   (`endpoint_zero_eq`, `periodize_eventuallyEq`, `eq_zero_of_mem_cube`) require a
   ball with closure inside the cube. The spec/brief interface uses the weaker
   `tsupport f ⊆ interior fundamentalCube`, which cannot call those lemmas
   directly (no ball to extract without a compactness detour). Re-derived the two
   tiny single-copy facts for the interior hypothesis
   (`periodize_eq_of_mem_interior`, `periodize_eventuallyEq_interior`) by
   mirroring `eq_zero_of_mem_cube` with `hmem := hsupp (subset_tsupport f hne)`;
   everything else (frontier nullity, `fderiv` vanishing, coordinate helpers) is
   reused from `T13.ConstantEndpoints`.

## Hypothesis weakening actually delivered

- Goal 1 needs only `tsupport f ⊆ interior fundamentalCube` — `ContDiff` is
  unused (`_hf`). The bridge holds for arbitrary `g`.
- Goal 2 needs `ContDiff ℝ ∞ f` (for the `gradientENorm`-identity measurability of
  `∇f`) and the interior support hypothesis; `periodize f`'s regularity is unused.

## Nothing left open

All three goals and every helper compile with axioms exactly
`[propext, Classical.choice, Quot.sound]`; `make check` is green. No residual
lemma, no `sorry`, no named input.
