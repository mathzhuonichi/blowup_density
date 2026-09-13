# B02 unit 8 (`cutoff_lebesgue` + `spatial_dense`) — attempts

Module: `formalization/NSFormalization/Section4/B02/Cutoff.lean`
Conformance: `research/B02/axioms_u8.lean`

## What was proved

* `cutoffLebesgue` (spec `Spec.lean:489-497`, `χ := baseCutoff`) — **fully**, no
  hypotheses. Both `L¹` and `L²` norms of `(1−χ_R)·schwartzVector ψ` tend to `0`.
* `spatialApproxHomogeneous_of` (concludes spec `spatialApproxHomogeneous`
  `Spec.lean:515-518`) — the diagonal assembly, **conditional** on units 2/6/7
  (`annularSchwartz`, `lebesgueHomogeneousDatum`, `homogeneousDatumSub`,
  `lowHighSplit`) taken as explicit hypotheses stated token-for-token from
  `Spec.lean`. It consumes the merged unit 1 (`annularRestriction`,
  `annularSmoothing` from `B02/Annular.lean`) and the in-module `cutoffLebesgue`.

`#print axioms` on both = `[propext, Classical.choice, Quot.sound]`.

## Design decisions (positive)

* **Smoothness / MemLp of `schwartzVector ψ`**: reused `contDiff_piLp`
  (`Mathlib/Analysis/Calculus/ContDiff/WithLp.lean:73`) and `memLp_piLp_iff`
  (`Mathlib/MeasureTheory/SpecificCodomains/WithLp.lean:30`) — the same route
  `Paper3/RealVectorPositiveDensity.lean` (`physicalVector_smooth`) takes. One
  line each.
* **Scalar cutoff tendsto** (`tendsto_eLpNorm_cutoff_compl`): built over `ℂ`,
  reusing the vendor `truncate` / `seminorm_truncate_sub_le`
  (`vendor/.../SchwartzCompactApproximation.lean`) to get `truncate g (max R 1) → g`
  in the Schwartz topology (via `schwartz_withSeminorms.tendsto_nhds_atTop`, the
  net indexed by real `R`), then `SchwartzMap.toLpCLM` continuity + `norm_toLp`
  to move to `(eLpNorm …).toReal → 0`, lifted back to `ℝ≥0∞` by
  `ENNReal.ofReal_toReal`. `(1−χ_R)g = −(truncate g R − g)` for `R ≥ 1`, so
  `eLpNorm` matches by `eLpNorm_neg`.
* **Vector → scalar** (`cutoffLebesgue`): each real component `ψ i` is complexified
  by `SchwartzMap.postcompCLM Complex.ofRealCLM`, the vector `eLpNorm` is bounded
  by `∑ᵢ` scalar `eLpNorm`s via a pointwise `‖v‖ ≤ ∑ᵢ‖vᵢ‖` bound
  (`norm_le_sum_norm`, `PiLp.norm_eq_of_L2` + `nlinarith`, as in
  `Annular.lean`'s `enorm_sub_lt_of_forall_le`) and `eLpNorm_sum_le`, then squeezed
  to `0` by `tendsto_of_tendsto_of_tendsto_of_le_of_le`.
* **Datum chain restated**: `SpatialField`, `VectorDistribution`,
  `IsSliceDistribution`, `IsHomogeneousDatum`, `IsHomogeneousVectorDatum`,
  `IsHomogeneousSliceDatum`, `homogeneousFourierENorm` copied token-for-token from
  `Data.lean`; `SplitRange`, `lowHighConstant`, `scaledCutoff`, `schwartzVector`
  from `Spec.lean`. `NSFormalization` cannot import `Contracts.V1.Data`, so this
  is the only way to state the spec fields; the conformance file discharges the
  Data-typed obligations by definitional equality.
* **Assembly**: `annularRestriction → annularSmoothing → annularSchwartz` gives a
  Schwartz field `h_n = schwartzVector ψ` with annular datum `W`; `cutoffLebesgue`
  + `lowHighSplit` give `homogeneousFourierENorm s ((1−χ_R)h_n) → 0`, so a single
  large `R` makes it `< ε/4` (found via `Tendsto.eventually_lt_const` on the
  low/high bound, whose two `L¹`/`L²` summands go to `0` after
  `ENNReal.continuous_rpow_const`); `homogeneousDatumSub` + `lebesgueHomogeneousDatum`
  give the datum `W − H_diff` of `χ_R h_n = h_n − (1−χ_R)h_n` with
  `‖H_diff‖ₑ = homogeneousFourierENorm …`. Triangle inequality in real norms
  (via `ofReal_norm`) sums the three `< ε/4` errors below `η`.

## Failures / fixes along the way

1. `SchwartzMap.toLpCLM ℂ ℂ p volume` → `typeclass instance MeasureSpace ?m stuck`:
   the domain `E` of the Schwartz map was undetermined. Fixed by pinning
   `(volume : Measure Space)`.
2. `tendsto_finset_sum` is deprecated → `tendsto_finsetSum`.
3. `(fun _ => zero_le _)` gave "function expected" and `zero_le'` is deprecated;
   used `fun _ => bot_le` (`⊥ = 0` in `ℝ≥0∞`).
4. `SchwartzMap.coe_sub` does not exist. `(S R − g) x = (S R) x − g x` and
   `truncate g R _ x = cutoff R x • g x` are both `rfl`, and the positivity proof
   inside `truncate` is proof-irrelevant, so `rw [hS]; show cutoff (max R 1) x • g x − g x = …`
   goes through by defeq.
5. `field_simp` left `errorTailBound = errorTailBound/ε * ε` unsolved; replaced by
   `div_lt_iff₀` + `mul_comm`.
6. `rw [hEq] at hc` failed because `Tendsto.comp` leaves the function as
   `ofReal ∘ (fun R => …)`, not the η-expanded form. Fixed with
   `hc.congr (fun R => ENNReal.ofReal_toReal (hfin R))`.
7. Conformance file: `FourierData` unknown until
   `open NSFormalization.Source.RealSobolev (FourierData)` was added (needed by
   the mirrored `IsAnnularDatum`).

## Alternatives rejected

* Assembling `schwartzVector ψ` as a genuine `SchwartzMap Space (EuclideanSpace ℝ (Fin 3))`
  and running `cutoffLebesgue` on it directly: the vendor `truncate` /
  `seminorm_truncate_sub_le` are `ℂ`-only, so this would require re-proving the
  Schwartz-topology tendsto for the Euclidean codomain. Component reduction reuses
  the vendor work instead.
* Abstracting `IsHomogeneousSliceDatum` as a variable predicate in
  `spatialApproxHomogeneous_of`: rejected — the task requires the hypotheses to be
  the spec fields verbatim, which needs the concrete restated chain so the
  conformance `example` matches by defeq.

## Commands run (from `verification/`, after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`)

* `lake build NSFormalization.Section4.B02.Cutoff` → `Build completed successfully (8815 jobs).`
  (no warnings/errors in `Cutoff.lean`).
* `lake env lean ../research/B02/axioms_u8.lean` → exit 0; both
  `#print axioms` print `[propext, Classical.choice, Quot.sound]`; both spec-typed
  `example`s type-check.
