# T12 tame-product proof attempts (lane 342)

## Route actually taken

- **Which extension of the convolution theorem.**  The brief allowed either the
  `L²` representation or a density argument.  **The `L²` representation was
  used.**  `MildPressure.periodicFourierCoeff_mul` assumes both factors are
  `C^∞`; inspecting its proof shows smoothness of the *first* factor enters
  only through (i) `Summable (fun l ↦ ‖f̂ l‖)` and (ii) the pointwise Fourier
  representation of `torusLift f`, while smoothness of the *second* factor
  enters only through integrability of `torusLift g`.  So the generalisation
  `periodicFourierCoeff_mul_of_series` takes exactly (i), an **a.e.** version
  of (ii), and integrability of the second lift, and repeats the same
  `integral_tsum_of_summable_integral_norm` argument with one extra
  `integral_congr_ae`.
  The a.e. version of (ii) (`torusLift_ae_eq_series`) is proved by comparing
  two `HasSum`s in `L²(T³)`: Mathlib's `UnitAddTorus.hasSum_mFourier_series_L2`
  applied to `MemLp.toLp (torusLift f)` (whose coefficients are the canonical
  ones by T10's `fourier_repr_toLp`), and the image under the continuous linear
  map `ContinuousMap.toLp` of the sup-norm-convergent series in
  `C(T³, ℂ)`.  `HasSum.unique` identifies the two limits; `MemLp.coeFn_toLp`
  and `ContinuousMap.coeFn_toLp` turn that into the a.e. statement.  No density
  argument and no `L¹`-Fourier-uniqueness lemma is needed.
- **Young `ℓ² ∗ ℓ¹ ⊆ ℓ²`** is proved from scratch (`torusYoungConvolution`):
  fibrewise Cauchy--Schwarz against the convolution measure
  `(∑ₗ Y(l)γ(k-l))² ≤ (∑ₗ Y(l)²γ(k-l))·‖γ‖₁`, then `HasSum.prod_fiberwise` on
  `(k,l) ↦ Y(l)²γ(k-l)` (whose total sum is `‖Y‖₂²‖γ‖₁` by the shift bijection
  `(k,l) ↦ (l, k-l)`, the same device as `PairingBound.sq_shift_sum'`).
  Mathlib's `Topology/Algebra/InfiniteSum/DiscreteConvolution.lean` only defines
  discrete convolution; it has no Young inequality, so nothing was reusable.
- **Peetre** is lane 336's `torusWeightPeetre`, at exponent `a = m/2` and hence
  with the factor `4^{m/2}` (the brief's `2^{m/2}` is not what the available
  lemma gives; `4^{m/2}` is used and is recorded in the constant).
- **The `ℓ¹` bound** `∑ₖ |â(k)| ≤ (∑ₖ W(k)^{-2})^{1/2} ‖a‖_{H²}` is the scalar
  mirror of `PairingBound.wAbs_zero_l1` (private there, so reproved), on top of
  lane 336's `torusInverseWeight_summable`.
- **The product's datum is constructed, not assumed**: `productCoeff` is the
  weighted convolution sequence, its `Memℓp 2` membership *is* the Young bound,
  periodicity comes from the factors and Haar integrability of the product lift
  from `MemLp.integrable_mul` on the two real `L²` lifts.
- **No named `Prop` input.**  Every statement in
  `Section3/T12/TameProduct.lean` is unconditional.

## Paths considered and rejected

- Minkowski in `ℓ²` was done through the `lp` norm (`realLp` + `norm_add_le`)
  rather than through the cruder `(x+y)² ≤ 2x² + 2y²`, which would have cost an
  extra `√2` in the constant for no saving in Lean work.
- Duality (`‖f‖₂ = sup_{‖X‖₂≤1} ∑ X f`) was rejected: it needs `f ∈ ℓ²`
  *before* the estimate, which is exactly what has to be proved.
- Reusing `PairingBound.torusTrilinearConvolution` directly was rejected for the
  same reason: it bounds a trilinear lattice sum, not an `ℓ²` norm.

## Resolved elaboration errors (exact text)

1. `periodicScalarSobolevENorm_eq`, wrong direction of the `le_iInf` goal:
   ```
   Application type mismatch: The argument
     Eq.symm (congrArg (fun C => ‖C‖ₑ) (scalarDatum_unique hA hB))
   has type ‖B‖ₑ = ‖A‖ₑ but is expected to have type ‖A‖ₑ = ‖↑⟨B, hB⟩‖ₑ
   ```
   Fix: drop the `.symm` (`le_iInf` leaves `‖A‖ₑ ≤ ‖B‖ₑ`, not the converse).
2. `scalarOrderDown` membership, `nlinarith` cannot cancel a squared `rpow`
   against a norm square (`logs/LESSONS.md`, 2026-09-18, same family):
   ```
   linarith failed to find a contradiction
   h1 : periodicFrequencyWeight k ^ ((s - r) / 2) ≤ 1
   h2 : 0 ≤ periodicFrequencyWeight k ^ ((s - r) / 2)
   a✝ : ‖↑A k‖ ^ 2 < (periodicFrequencyWeight k ^ ((s - r) / 2)) ^ 2 * ‖↑A k‖ ^ 2
   ⊢ False
   ```
   Fix: an explicit `calc` through `mul_le_mul_of_nonneg_right ht2 (sq_nonneg _)`
   with `ht2 : t ^ 2 ≤ 1` proved separately by `nlinarith`.
3. `memLp_lift_ofReal`: `simp` will not unfold the `torusLift` of a
   complexified real field, leaving
   ```
   unsolved goals ⊢ ‖torusLift (fun x => ↑(z x)) q‖ = |torusLift z q|
   ```
   Fix: `show ‖((torusLift z q : ℝ) : ℂ)‖ ≤ ‖torusLift z q‖` (the two lifts are
   definitionally equal) and then `rw [Complex.norm_real]`.
4. Argument order of `ContinuousMap.coeFn_toLp` differs from
   `ContinuousMap.toLp`: `toLp` takes `p μ 𝕜` explicitly, but `coeFn_toLp` is
   stated after `variable {p}` / `variable {𝕜}`, so its first explicit argument
   is the *measure*.  `ContinuousMap.coeFn_toLp (E := ℂ) 2 periodicTorusMeasure ℂ g`
   fails with
   ```
   failed to synthesize instance of type class OfNat (Measure ?m.387) 2
   ```
   Fix: named arguments, `ContinuousMap.coeFn_toLp (E := ℂ) (𝕜 := ℂ) (p := 2)
   periodicTorusMeasure g`.
5. Probe: `simp only [probeFreq, Pi.neg_apply, if_pos rfl] at h0` leaves the
   `if` unreduced and then
   ```
   omega could not prove the goal: No usable constraints found.
   ```
   Fix: plain `simp [probeFreq, Pi.neg_apply] at h0` closes the goal outright.
6. Probe: `if_pos` / `if_neg` are deprecated at `v4.34.0-rc2`
   (`logs/LESSONS.md`, 2026-09-18).  Replaced every `simp only [..., if_pos ...]`
   by named helper lemmas (`probeCoeff_pos`, `probeCoeff_neg`,
   `probeCoeff_eq_zero`) proved with plain `simp [probeCoeff, h…]`.
7. Unused-tactic linter fired on `congr 1 <;> exact congrArg Real.sqrt ...`
   after the `lp_norm_eq_sqrt` rewrites: `realLp_apply` is `rfl`, so the two
   sums are already definitionally equal and `exact hb` suffices.

## Residual named inputs

None.  There is no `def … : Prop` input anywhere in the module; `tameProduct`
is unconditional.
