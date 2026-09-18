# Lane 354 — T13 §2 kernel comparison with the paper's geometric constant (Opus prover; transcribed by the lead from the agent's final message — report-file guard)

Commit `94d623f5f40ddcd0eefb102b943303024bef6560` on `erenup/354-T13-kernel-comparison` (stacked on lane 353). No `sorry`/`admit`/`axiom`/`native_decide`, no named input, no `maxHeartbeats` override; 25 declarations, all `[propext, Classical.choice, Quot.sound]`.

## 1. What was proved (`Section3/T13/KernelComparison.lean`, namespace `NSFormalization.Section3.T13`)
The four residual items of `ATTEMPTS_LOCALIZATION_KERNEL.md` — each brief statement was checked against `03-torus.tex:79-92` and found true as written:
1. `exists_separation (hr : 0 < r) (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) : ∃ δ, 0 < δ ∧ closure (Metric.ball c r) ⊆ {x | ∀ i, δ ≤ x i ∧ x i ≤ 1 - δ}` (witness `separationRadius c r = ⨅ᵢ min (cᵢ − r) (1 − cᵢ − r)`).
2. `tailGeomConst s c r : ℝ≥0∞ := (ofReal (tailGeomC0 c r)) ^ (-(3 + 2s)) * tailSum s`, `tailGeomC0 c r = min (1/2) (separationRadius c r / (2√3))`; `tailGeomConst_lt_top (hs : 0 < s) …`; `latticeTail_le_tailGeomConst (hs : 0 ≤ s) … : ∀ x ∈ closure (ball c r), ∀ y ∈ fundamentalCube, latticeTail s (x − y) ≤ tailGeomConst s c r` (the two regimes `≥ δ` / `≥ |n|/2` fused into `|x − y + n| ≥ c₀|n|`, `geom_norm_lower`).
3. `iTorus_singular_le (hfc : Continuous f) : ∫⁻ x in Q, ∫⁻ y in Q, ofReal ‖f x − f y‖² · fractionalRadialKernel s (x − y) ≤ IReal s f`.
4. `iTorus_periodize_le (hs : 0 < s) (hs1 : s < 1) (hr : 0 < r) (hball) (hf : ContDiff ℝ ∞ f) (hsupp : SupportedInBall c r f) : ITorus s (periodize f) ≤ IReal s f + 4 * tailGeomConst s c r * (eLpNorm f 2 volume) ^ 2` (`eq:localization`'s kernel step).
Helpers: `latticeVector_norm_ge_one`, `latticeTail_neg`, `ball_coord_bounds`, `separationRadius(_le,_pos)`, `closedBall_coord_sep`, `norm_sub_le_sqrt3`, `tailGeomC0(_pos)`, `geom_norm_lower`, `measurable_latticeTail/_prod_frac/_prod_tail/_inner_frac`, `periodicKernel_split`, `volume_fundamentalCube`, `sq_eLpNorm_two`. Reused: 345's `lintegral_whole_shift`, `measurable_prod_diff`, `latticeVector_apply/_neg`, `toSpace_preimage_fundamentalCube`; 344's `periodize_eq_of_mem_cube`, `interior_fundamentalCube`, `abs_spaceCoord_le_norm`, `latticeVector_zero`; 353's `tailSum`/`tailConst_lt_top` pattern.

## 2. Files
`formalization/NSFormalization/Section3/T13/KernelComparison.lean`; `research/T13/probes/kernel_comparison_closes.lean` (four items on the lane-344 `ContDiffBump` field + the lane-359 consumer `example`); `research/T13/axioms_kernel_comparison.lean` (25); `research/T13/ATTEMPTS_KERNEL_COMPARISON.md`; status in `research/T13/COMPARISON.md`.

## 3. Gap
None in this lane. Lane 359 (assembly of the `localization` field) needs: the `L²` half through the Parseval-at-0 bridge (`Section3/T15/ParsevalZero.lean`, #331) + `endpoint_zero`; the homogeneous half through `torus_identity`, `constant_pos_finite` (division by `cFrac s`) and the square root of this lane's bound; both sketched in the probe's consumer `example`.
Implementation notes: under this pin the monotone-mul lemmas are renamed (`mul_le_mul_left'` → `mul_le_mul_right`, `mul_le_mul_right'` → `mul_le_mul_left`); `tsum_subtype`'s `↥{n | n ≠ 0}` is only defeq to `{n // n ≠ 0}`, so `rw [tsum_subtype …]` fails — state a typed `have` and let elaboration close the defeq.

## 4. Commands and results
`lake build NSFormalization.Section3.T13.KernelComparison` → success (9994 jobs), 0 errors, 0 module warnings; axioms file → 25 × standard; probe → no errors; `make check` → OK.
