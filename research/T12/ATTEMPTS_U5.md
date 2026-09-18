# T12 U5 (lane 400) — attempts, positive and negative

Target: the `gradientLSix` field of `MeanZeroSobolevCalculusAPI`
(`research/T12/probes/api_on_canonical.lean:184-187`), route (c) of
`research/T12/T12_SPLIT.md`.  Result module:
`formalization/NSFormalization/Section3/T12/GradientLSix.lean`.  **Closed, no
named input.**

## 1. Route actually used

`‖∇v‖₆(T³)` → cube norm (`HaarCube.periodicLpENorm_eq_restrict_gradientTensor`)
→ `∇(χv)` on the cube (χ ≡ 1 on `ball 0 (5/2) ⊇ [0,1]³`, so the two gradients agree
there; `gradTensor_cutoffMul_eqOn`) → whole-space norm (`Measure.restrict_le_self`)
→ registered `A05.eLpNorm_gradTensor_six_le` on `χv` (`smoothL2_cutoffMul`:
smooth + compact support ⇒ `SmoothL2`) → Leibniz `Δ(χv) = χΔv + 2∑ᵢ(∂ᵢχ)(∂ᵢv) + (Δχ)v`
(`lap_cutoffMul_eq`) → pointwise majorant `leibnizConst·(‖Δv‖+‖∇v‖+‖v‖)` supported in
`tsupport χ = closedBall 0 3` → lattice tiling
(`T13.lintegral_eq_tsum_halfOpenCube` + lane-377 `CutoffGagliardo.lattice_count_le`,
count `7³ = 343`) → one cube → the two torus lower-order bounds.

The two torus bounds are the only genuinely new Fourier work:

* `periodicLpENorm_two_le_laplacian`: reweight the order-2 datum by
  `1/(1+4π²|k|²) ≤ 1` (`SpectralGap.reweightDatum`, real even multiplier), then
  `T10.parseval_forward` identifies the order-0 datum norm with `‖v‖_{L²(T³)}`, then
  `FourierEmbeddings.hTwo_le_laplacian`.
* `periodicLpENorm_gradientTensor_le_laplacian`: `T10.gradient_eq_homogeneousENorm`
  gives `‖∇v‖_{L²(T³)} = ‖meanZeroPartT v‖_{Ḣ¹(T³)}`, and `meanZeroPartT v = v` for
  mean-zero `v` (lane 377 `meanZeroPartT_eq_self`); then reweight the order-2 datum by
  `|2πk|/(1+4π²|k|²) ≤ 1` to get `Ḣ¹ ≤ H²` and apply `hTwo_le_laplacian` again.

## 2. Rejected routes (negative record)

* **Complex Fourier multiplier for `‖∂ⱼv‖_{L²(T³)}`.**  The direct reduction
  `∂ⱼv ← Δv` has symbol `2πi kⱼ/(-4π²|k|²)`, which is purely imaginary;
  `SpectralGap.reweightDatum` only accepts a **real** multiplier
  (`w : PeriodicFrequency → ℝ`) and `reweightDatum_real` needs `w(-k) = w(k)`.  A
  complex/odd-imaginary variant would have to be re-proved (carrier `ℓ²` membership,
  norm bound, conjugate-reflection submodule) — roughly 100 lines.  Avoided entirely by
  going through `gradient_eq_homogeneousENorm`, where the multiplier `|2πk|` is real
  and even.
* **Caccioppoli / whole-space integration by parts** (`‖∇w‖² = -⟨w,Δw⟩` on the
  compactly supported `ψv`) to bound `‖∇v‖_{L²}` without Fourier.  Abandoned before
  writing Lean: it produces a self-referential quadratic `X² ≤ aV L + bVX` that has to
  be solved in `ℝ≥0∞`, which is strictly worse than the 40-line Fourier reweight.
* **Named input.** None used; the unit has no `def … : Prop` hypothesis.

## 3. Pin-specific failures hit while writing the proof (all fixed)

1. `HasCompactSupport.sum` — **unknown constant** on this Mathlib pin.  Fix:
   `Fin.sum_univ_three` + `HasCompactSupport.add` three times
   (`hasCompactSupport_lap`).
2. `rw [fderiv_smul …]` / `rw [fderiv_add …]` fail against a goal written
   `fderiv ℝ (fun y => c y • w y) x`: the library lemmas are stated for the Pi
   operations `c • w` and `f + g`.  Fix: `show fderiv ℝ (c • w) x (coordinateVector i) = _`
   first (`dirDeriv_smul_eq`, `dirDeriv_add_eq`).
3. `abel` fails on the second-derivative rearrangement `(A+B)+(B+C) = A+(B+B)+C`
   where `B = r • y` with an `ℝ`-smul: it normalizes `B + B` to the `ℕ`-smul `2 • B`
   on one side only and reports "unsolved goals" (suggesting `abel_nf`).  Fix:
   `simp only [add_assoc]`.
4. `simp only [homogeneousDatumWeight, hk, ↓reduceIte, Real.sqrt_eq_rpow]` leaves the
   goal `(periodicAngularFrequencySq k).rpow (1/2) = periodicAngularFrequencySq k ^ (1/2)`
   (the definition writes `Real.rpow` explicitly, the lemma writes `^`); `simp` will not
   close it but `rfl` does.
5. `positivity` cannot discharge `0 ≤ 2 * hTwoConst` / `0 ≤ homogeneousDatumWeight 1 k /
   periodicFrequencyWeight k`: both involve opaque `def`s.  Fix: bring
   `hTwoConst_pos` / `fourierWeight_pos` into context and use `linarith` /
   `div_nonneg`.
6. `eLpNorm_const_smul_le` takes **no explicit arguments** on this pin
   (`eLpNorm_const_smul_le _ _` is "function expected"), and it will not unify
   `leibnizMajorant v` with `?c • ?f`.  Fix: a `rfl`-rewrite
   `leibnizMajorant v = leibnizConst • (fun x => …)` before applying it.
7. `if_neg` is deprecated (`ite_eq_right`); `continuous_finset_sum` is deprecated
   (`continuous_finsetSum`).  Both produce warnings, which the `lake env lean`
   zero-output gate treats as failures.

## 4. Known gap / honest limitation

`Csix = 343 · gradientL6Const · leibnizConst · (1 + 2·hTwoConst)` is a closed real
term but **not a numeral**: `leibnizConst = 1 + 6·cutoffGradBound + cutoffLapBound` is
built from `Classical.choose` of the two sup bounds of the lane-365 cutoff
(`Cutoff.exists_cutoff_fderiv_bound` and the new `exists_cutoff_lap_bound`), which
`Cutoff.lean` only exposes as existentials, and `gradientL6Const` itself contains
Mathlib's irreducible `eLpNormLESNormFDerivOfEqInnerConst`.  The same opacity is
already accepted upstream in `Section4/A05/GradientL6.lean:52`.  Making `Csix`
numeric would require explicit `C⁰/C²` bounds for `ContDiffBump`, which Mathlib does
not provide.

Non-vacuity is exhibited in `research/T12/probes/gradient_l6_closes.lean` on the
nonzero smooth mean-zero periodic witness `probeMZ` (the lane-377 single cosine mode
made mean-free).  Not proved (and not required by the field): that the left-hand side
is nonzero at that witness.
