# ATTEMPTS — T20 U10b `hOneEnergy` (`eq:H1energy`, `03-torus.tex:467-484`), lane 432

Target: the `hOneEnergy` field of `CriticalRegularityTAPI`
(`Section3/T20/CriticalRegularity.lean:330-342`) verbatim.
Result: **closed, no named input, no residual**, at
`c = criticalSmallnessH1 = min criticalSmallness (1/(8·h1TrilinearConst))`, `CH1 = 2`.
Module `formalization/NSFormalization/Section3/T20/H1Energy.lean` (31 declarations).

## What the route actually needed (vs. the brief / the split)

* **U6 `meanFreeEquation` is not a dependency.**  As with U8 and U5, the whole
  computation runs on the Fourier side through U8's `rawEnergyDeriv_split`
  (= T11's `freqEnergyDerivT_split` at order `0`, applied to the *full* velocity
  and force), U8's `advection_mean_split`, and U8's `re_sum_conj_fderiv_dir_zero`.
  The mean-free reduction happens frequency by frequency (the order-one weight
  `|2πk|²` kills `k = 0`), so the physical equation for `v` is never formed.
  `T20_SPLIT.md` lists "Deps: U6, U9, U10a"; the real dependency set is U8
  (through `YBound`), U9 and U10a.
* **`HighOrder.lean:312,345,367` (the pressure / mean-transport drops) are not
  used.**  The pressure term has already dropped inside `rawEnergyDeriv_split`;
  the mean transport drops by `re_sum_conj_fderiv_dir_zero`, which is
  weight-independent and therefore reusable verbatim at the order-one weight.
* **`HighOrder.lean:386 torusYoungAbsorb` is not used.**  Its shape is
  `½d + νg² ≤ C·a·n·g + F·n ⟹ ½d ≤ C²/(4ν)a²n² + F·n`, i.e. absorption of a
  *cross term* into the dissipation — the high-order chain's shape, not
  `2ab ≤ (ν/2)a² + (2/ν)b²`.  The Young step here is three lines inline
  (identity `ν/2·a² + 2/ν·b² − 2ab = (νa − 2b)²/(2ν)`).
* **The one genuinely new analytic input** is the order-`2` Parseval identity
  `‖Δz‖_{L²(T³)} = ‖z − ∫z‖_{Ḣ²(T³)}`
  (`periodicLpENorm_two_laplacian_eq_homogeneous`), the order-`2` analogue of
  T10's `gradient_eq_homogeneousENorm` (`ForcePaths.lean:357`), which did not
  exist.  Proof: the order-`0` datum of `Δz` is the *negative* of the order-`2`
  homogeneous datum of the mean-free part of `z`, frequency by frequency
  (`T10.periodicFourierCoeff_vector_laplacian` gives `−|2πk|²ẑ`, and
  `homogeneousDatumWeight 2 k = |2πk|²`), so the two `ℓ²` norms agree by
  `enorm_neg`.  ~30 lines.
* **The force term is done on the coefficient side, not in physical space.**
  Because `PeriodicSobolev s` is an `abbrev` with a *phantom* `s`
  (`PeriodicData.lean:98`), `T11.hasSum_datum_pair` and `T11.torusRealPairing_le`
  can pair the order-`2` homogeneous velocity datum against the order-`0` force
  datum directly, giving `∑ₖ|2πk|²Re∑ᵢ conj(ûᵢ)ĝᵢ ≤ ‖Δv‖₂‖h‖₂` with no new
  torus Hölder/Cauchy–Schwarz.  `s` is an unresolved metavariable in that
  situation, so both calls need an explicit `(s := (2 : ℝ))`.
* **`∇v = ∇u` and `Δv = Δu`** for `v = u − m(t)` (`gradientTensor_sub_const`,
  `laplacian_sub_const`, via `fderiv_sub_const`) removes every `meanZeroPartT`
  idempotence step from §5; only the *coefficients* need the mean-free bridge.

## Arithmetic, in full

`E' = −2ν‖Δv‖₂² + 2·P_force + 2·Q_conv` with
`P_force ≤ ‖Δv‖₂‖h‖₂` and `Q_conv ≤ C₁·y·‖Δv‖₂²`.
`y ≤ ρ < c·ν` (U9 `yBound_of_le`) and `c ≤ 1/(8C₁)` give `2Q_conv ≤ (ν/4)‖Δv‖₂²`;
Young gives `2‖Δv‖₂‖h‖₂ ≤ (ν/2)‖Δv‖₂² + (2/ν)‖h‖₂²`.  Hence
`E' + ν‖Δv‖₂² ≤ −(ν/4)‖Δv‖₂² + 2ν⁻¹‖h‖₂² ≤ 2ν⁻¹‖h‖₂²`, so **`CH1 = 2`**.

## Failed attempts / pin-specific traps (one compile round each)

1. `rw [..., Real.rpow_one]` for `homogeneousDatumWeight 2 k = |2πk|²`:
   ```
   error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
     ?x ^ 1
   in the target expression
     (periodicAngularFrequencySq k).rpow 1 = periodicAngularFrequencySq k
   ```
   `homogeneousDatumWeight` is defined with `Real.rpow` in *application* form, so
   the `^` notation of `Real.rpow_one` does not match under `rw`.  Fix: rewrite
   the exponent first (`show (2:ℝ)/2 = 1`), then `exact Real.rpow_one _`.
   (Same trap as T10's own `homogeneousDatumWeight_one`, which ends in `rfl`.)
2. `rw [hA.2.2.2 i k, Complex.real_smul]` on the homogeneous datum clause:
   ```
   error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
     ?m • ?m'
   ```
   The clause is already a **ℂ**-smul (`(homogeneousDatumWeight s k : ℂ) • …`);
   `smul_eq_mul` is the lemma.  This is U8's recorded trap, hit again.
3. **Sign of the convection term.**  `hasSum_angularPairing` targets
   `−periodicPairing (Δv) N`, and the combination *subtracts* `2·` that, so the
   convection enters as `+2·periodicPairing (Δv) N` — the bound needed is
   `le_abs_self`, not U8's `neg_le_abs` (U8's `hconv` targets `+periodicPairing`).
   Using `neg_le_abs` produced
   `error: H1Energy.lean:682:2: linarith failed to find a contradiction`
   at the last line, with everything else already proved.
4. **Young by `rw`-surgery.**  First version:
   `rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_nonneg]` … then
   `rw [div_add_div _ _ … ] at *` … `nlinarith [...]` →
   `error: H1Energy.lean:677:4: linarith failed to find a contradiction`.
   Replaced by: state the identity
   `ν/2·a² + 2/ν·b² − 2ab = (νa − 2b)²/(2ν)` (`field_simp; ring`), add
   `div_nonneg (sq_nonneg _) (by linarith : (0:ℝ) ≤ 2*ν)`, close with plain
   `linarith`.  The final assembly is likewise plain `linarith` once
   `mul_nonneg hν.le (sq_nonneg aL)` is supplied — no `nlinarith` anywhere in the
   module.
5. Lane 429's blocker (`contDiff_dirDeriv` declared in both `GradientLSix` and
   `GradientLambdaL3`) is **gone**: lane 427 moved it to `T12/DirDeriv.lean`, so
   `import YBound + H1Trilinear` (the `GradientLambdaL3` and `GradientLSix` sides
   together) builds.  Verified before writing a line of the module.

## Constant choice

`criticalSmallnessH1 := min criticalSmallness (1/(8·h1TrilinearConst))`, with
`criticalSmallness = 1/(8·criticalTrilinearConst)` from U9.  Exported:
`criticalSmallnessH1_pos`, `criticalSmallnessH1_le_half` (so U9's `yBound_of_le`
applies verbatim), `criticalSmallnessH1_lt_quarter_C₀` (the structure's strict
`c < 1/(4C₀)`), `criticalSmallnessH1_le_eighth_C₁` and
`criticalSmallnessH1_lt_quarter_C₁` (the structure's strict `c < 1/(4C₁)`).
U13 installs `c := criticalSmallnessH1`, `C₀ := criticalTrilinearConst`,
`C₁ := h1TrilinearConst`, `CH1 := 2`.  U8's `criticalEnergy` and U9's
`yBound_of_le` are both available at this smaller `c` without reproving anything;
U9's `yBound` itself is stated at `criticalSmallness`, so U13 must use
`yBound_of_le criticalSmallnessH1_le_half`, exactly as this module does.
