# C01 unit U6 — implementation notes

Unit U6 of `research/C01/COMPARISON.md:176`: spec fields `trilinearHolder`,
`trilinearAbsorbed`, `laplacianSqENorm` of
`BlowupDensity.C01.Draft.EnergyAbsorptionAPI` (`research/C01/Spec.lean:410-473`).

Module: `formalization/NSFormalization/Section4/C01/Trilinear.lean`.
Conformance: `research/C01/axioms_u6.lean` (3 `example`s in contract vocabulary
+ `#print axioms`, all `[propext, Classical.choice, Quot.sound]`).

## Route actually used

**No `MemLp z 3` interpolation.** COMPARISON §1 suggested obtaining `MemLp z 3`
by interpolating the jet class (`L²`) and `smooth_memLp_six`, needed only for a
*Bochner* (real-integral) route. I did the trilinear Hölder entirely in `ℝ≥0∞`,
so the inequality holds unconditionally and needs no membership/finiteness — only
measurability, which smoothness supplies. `smooth_memLp_six` is therefore **not**
used by U6.

**The price of the `ℝ≥0∞` route, and how it is paid (review finding 1).** Working
in `ℝ≥0∞` makes `trilinearHolder`/`trilinearAbsorbed` unconditional, but that is
*not free*: the left side is `ENNReal.ofReal |advectionWork z|` and `advectionWork z`
is a Bochner integral, which Mathlib evaluates to junk `0` when the integrand
`⟨(z·∇)z, Δz⟩` is not integrable — so the two fields alone do not certify that
`advectionWork z` is the true integral (the Bochner route would have produced
integrability as a by-product; this route does not). The obligation the
specification parks on `velocityJets`/`enstrophyIdentity` is now paid here:
* `lintegral_advection_inner_laplacian_le` — the hoisted core, whose left side is
  `∫⁻ ‖⟨(z·∇)z, Δz⟩‖ₑ` (enorm of the **integrand**, not of the formed integral).
* `integrable_advection_inner_laplacian` (one line): `criticalL3 z ≠ ⊤ →
  Integrable (fun x => ⟨(z·∇)z x, Δz x⟩)`. Each factor of the bound is finite —
  `criticalL3 z` by hypothesis, `eLpNorm (∇z) 6` by the registered `L⁶` clause,
  `eLpNorm (Δz) 2` by `MemLp (lap z) 2` (`MemLp.eLpNorm_lt_top`) — so
  `∫⁻ ‖·‖ₑ < ⊤`, i.e. `hasFiniteIntegral_iff_enorm`; `AEStronglyMeasurable` comes
  from continuity of the inner product (`ContDiff.continuous_fderiv` +
  `Continuous.clm_apply` + `Continuous.inner`). U7's `enstrophyIdentity`, an
  equality containing the same `advectionWork`, relies on this to avoid the junk
  value. `trilinearHolder` now factors through the named lemma.

Chain for `trilinearHolder`:
1. `ENNReal.ofReal |advectionWork z| = ‖advectionWork z‖ₑ` (`Real.enorm_eq_ofReal_abs`).
2. `‖∫ ⟨(z·∇)z, Δz⟩‖ₑ ≤ ∫⁻ ‖⟨(z·∇)z, Δz⟩‖ₑ` (`enorm_integral_le_lintegral_enorm`,
   unconditional — no integrability side goal).
3. Pointwise `‖⟨(z·∇)z (x), Δz x⟩‖ₑ ≤ ‖z x‖ₑ · ‖∇z x‖ₑ · ‖Δz x‖ₑ`, from
   * `abs_real_inner_le_norm` (Cauchy–Schwarz on the inner product), and
   * `advection_norm_le` (below), lifted to `ℝ≥0∞` via `ENNReal.ofReal_mul` +
     `ofReal_norm`.
4. `lintegral_mono` + three-factor Hölder `ENNReal.lintegral_prod_norm_pow_le`
   over `Fin 3` with `p = ![1/3, 1/6, 1/2]` (sum `= 1`), each factor
   `f i = ‖·‖ₑ ^ kᵢ`, using `Fin.prod_univ_three` and
   `eLpNorm_eq_lintegral_rpow_enorm_toReal` to reassemble
   `(∫⁻ ‖z‖ₑ³)^{1/3} = eLpNorm z 3`, etc. `(a^k)^{1/k} = a` via `ENNReal.rpow_mul`.

`advection_norm_le`: `advection (lift z) 0 x = fderiv ℝ z x (z x)` (`rfl`);
`fderiv ℝ z x (z x) = ∑ⱼ (z x)ⱼ • ∂ⱼz(x)` (basis expansion + `map_sum`/`map_smul`);
then `norm_sum_le`, `Real.sum_mul_le_sqrt_mul_sqrt` (finite Cauchy–Schwarz),
`EuclideanSpace.norm_eq` and `PiLp.norm_eq_of_L2` to identify the two `√(∑ ·²)`
factors with `‖z x‖` and `‖gradTensor z x‖`.

`trilinearAbsorbed`: `trilinearHolder` then the registered
`NSFormalization.Section4.A05.eLpNorm_gradTensor_six_le` (the local theorem that
`Contracts.V1.GradientL6API.gradientLSix` binds to, per
`verification/Bindings/GradientL6.lean:46`), `mul_le_mul'`, and
`ENNReal.rpow_two` + `ring` to collect `‖Δz‖₂ · ‖Δz‖₂ = ‖Δz‖₂²`.
**`C₁ = NSFormalization.Section4.A05.gradientL6Const = gradientL6.Csix`.**

`laplacianSqENorm`: `MemLp (lap z) 2` (`memLp_finsetSum` over the three columns),
`MemLp.integrable_norm_rpow` → `Integrable ‖Δz‖²`, then square the tree lemma
`NSFormalization.Section4.I02.eLpNorm_two_eq_ofReal_sqrt` with
`ENNReal.ofReal_rpow_of_nonneg`, `Real.rpow_two`, `Real.sq_sqrt`.

## Definitional bridges (why `formalization/` theorems discharge the spec fields)

`formalization/` cannot import `Contracts.*`. The three fields are stated against
the A05 objects the registered contract binds to, which are `rfl`-equal to the
contract's (`verification/Bindings/GradientL6.lean:27-37`):
`Contracts.V1.gradientTensor = A05.gradTensor`, `Contracts.V1.laplacian = A05.lap`,
`Contracts.V1.SmoothSquareIntegrableJets = A05.SmoothL2`. §0 restates the spec
`def`s `lift`, `advectionWork`, `criticalL3`, `laplacianSq`. The conformance file
restates the same `def`s in contract vocabulary and closes the three field
statements by `exact` (defeq).

## Failures / dead ends hit during iteration

* `PiLp.continuous_toLp.comp …` for `Continuous (gradTensor z)` failed: `.comp`
  resolved as `Function.comp`, and `PiLp.continuous_toLp` takes `p` and `β`
  **explicitly** (`∀ (p) {ι} (β) [inst], Continuous (WithLp.toLp p)`). Fixed with
  `show Continuous (fun x => WithLp.toLp 2 (fun j => dirDeriv j z x))` then
  `Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Space)) (continuous_pi …)`.
* `mul_le_mul_right'` / `mul_le_mul_left'` were not in scope for `ℝ≥0∞`; used
  `mul_le_mul'` (nested) instead.
* `Real.mul_self_sqrt` expects `√a * √a`; after `Real.rpow_two` the term is
  `√a ^ 2`, so `Real.sq_sqrt` is the right lemma.
* `norm_num` (after `Fin.sum_univ_three`) reduces `![…] 0` and `![…] 1` but
  **not** `![…] 2`; had to pass `Matrix.cons_val_two, Matrix.tail_cons,
  Matrix.head_cons` to the `hp : ∑ p = 1` `norm_num`. **Correction to an earlier
  guess** (review finding 2): the blocker is `norm_num`-specific, *not* simp-tagging
  — plain `simp [Fin.sum_univ_three]` on this pin **does** reduce `![…] 2` (leaving
  `3⁻¹ + 6⁻¹ + 2⁻¹ = 1` for arithmetic), so `Matrix.cons_val_two` being `rfl`/not
  `@[simp]` is not the discriminator; it is only that `norm_num`'s internal
  simp set does not reduce that index. After `fin_cases`, index 2 reduces
  without those lemmas (defeq), so `h2p` and the `hf` measurability cases needed
  no `Matrix.*` simp args.
* Deprecated `continuous_finset_sum` → `continuous_finsetSum`.

## Commands

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.Trilinear
  → Build completed successfully (9354 jobs).   # sorry-free, no warnings on the module
cd verification && lake env lean ../research/C01/axioms_u6.lean
  → 5 × "depends on axioms: [propext, Classical.choice, Quot.sound]", no errors
    (trilinearHolder, trilinearAbsorbed, laplacianSqENorm,
     lintegral_advection_inner_laplacian_le, integrable_advection_inner_laplacian)
cd .. && make check
  → check_formalization_plan / check_contracts / test_contract_policy /
    check_work_queue all pass, exit 0
```
