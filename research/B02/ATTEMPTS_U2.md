# B02 unit 2 (`annularSchwartz`) — attempts

Module: `formalization/NSFormalization/Section4/B02/AnnularSchwartz.lean`
Conformance: `research/B02/axioms_u2.lean`
Split table: `research/B02/U2_SPLIT.md`

## What was proved (this run)

* **SL1** `contDiff_rpow_mul_of_annulus` — the homogeneous weight
  `((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ` is `ContDiff ℝ ∞` with `HasCompactSupport`, for any
  real `s`, given `0 < δ`, `g` smooth, `tsupport g ⊆ closedFrequencyAnnulus δ R`.
* **SL2** `exists_schwartz_angularFourier_eq` — every smooth compactly supported
  `f : Space → ℂ` equals `angularFourier φ` (pointwise) for a Schwartz `φ`.
* helper `schwartzAngularDilation_dilationInv` — right inverse of the normalized
  angular dilation on `𝓢(Space,ℂ)`, `:= schwartzAngularDilationEquiv.right_inv X`
  (the `right_inv` field of the **public** equiv `schwartzAngularDilationEquiv`,
  `AngularFourierDilation.lean:48-64`). (First draft re-proved it inline by `ext` +
  `simp` + a re-derivation of `amplitude_inverse`; that was wrong-headed — the
  private `amplitude_inverse` is irrelevant, the public `right_inv` field discharges
  it in one line. Corrected per lane-078 review finding 2.)

`#print axioms` on all three = `[propext, Classical.choice, Quot.sound]`.
Unit 2 as a whole is **not** complete: SL3 (reality) and SL4a/b/c + assembly remain
(sizes in `U2_SPLIT.md`).

## Design decisions (positive)

* **SL1 smoothness by point split, not open cover.** `contDiff_iff_contDiffAt`, then
  `by_cases ξ₀ = 0`.  At `ξ₀ = 0` the datum vanishes on `(tsupport g)ᶜ ∈ 𝓝 0`
  (because `‖0‖ = 0 < δ`), so `contDiffAt_const.congr_of_eventuallyEq` with
  `image_eq_zero_of_notMem_tsupport`.  Off the origin, `contDiffAt_norm ℝ hξ`
  (`InnerProductSpace/Calculus.lean:154`, `𝕜 = ℝ` explicit) →
  `ContDiffAt.rpow_const_of_ne` (`Pow/Deriv.lean:624`, needs `‖ξ₀‖ ≠ 0` via
  `(norm_pos_iff.mpr hξ).ne'`) → `Complex.ofRealCLM.contDiff.comp_contDiffAt` for the
  coercion → `ContDiffAt.mul` against `hg.contDiffAt`.  The two-way split cleanly
  isolates the only non-smooth point of `‖·‖ ^ (-s)`.
* **SL1 compact support.** `tsupport g ⊆ closedFrequencyAnnulus δ R ⊆ closedBall 0 R`
  (compact via `isCompact_closedBall`, as in `Annular.lean:319`), so
  `HasCompactSupport g` by `IsCompact.of_isClosed_subset`; then
  `HasCompactSupport.mul_left` (`Topology/Algebra/Support.lean:483`) since `g` is the
  right factor.  The rewrite `(fun ξ => a ξ * g ξ) = (fun ξ => a ξ) * g` is `rfl`.
* **SL2 by Fourier inversion.** The angular transform is
  `angularFourier ↑φ ξ = schwartzAngularDilation (𝓕 φ) ξ` (`rfl`, `AFD:208`), so the
  inverse is `φ := 𝓕⁻ (schwartzAngularDilationInv (ofCompactSupport f))` using the
  Mathlib Schwartz-level `FourierTransform`/`FourierInvPair` instances
  (`SchwartzSpace/Fourier.lean`), whose `fourier_fourierInv_eq : 𝓕 (𝓕⁻ f) = f`
  collapses the round trip; the dilation round trip is the helper above.  The final
  goal `(ofCompactSupport f) ξ = f ξ` is `ofCompactSupport_apply`.  No integrals, no
  seminorm estimates — all at the Schwartz-map/CLE level.

## Failures / fixes along the way

1. **`simpa [Function.comp] using hcomp`** for the `ℝ→ℂ` coercion did **not** unfold
   `⇑Complex.ofRealCLM ∘ (fun ξ => ‖ξ‖ ^ (-s))`, leaving a type mismatch against
   `fun ξ => ↑(‖ξ‖ ^ (-s))`.  Passing the plain `def` `Function.comp` to `simp` does
   not rewrite the composition here.  **Fix:** ascribe the `comp_contDiffAt` result to
   the lambda form `fun ξ => Complex.ofRealCLM (‖ξ‖ ^ (-s) : ℝ)` (defeq to `∘`), then
   `simpa only [Complex.ofRealCLM_apply]` (a `@[simp] rfl`) to turn
   `Complex.ofRealCLM x` into `↑x`.
2. **`fourier_fourierInv_eq` unknown identifier.**  It is `export`ed into namespace
   `FourierTransform` (`Analysis/Fourier/Notation.lean:222`), which `open scoped
   FourierTransform` does **not** bring into scope (scoped opens the notation only).
   **Fix:** qualify as `FourierTransform.fourier_fourierInv_eq` (it is also `@[simp]`,
   so `simp` would work too).

## Notes for the remaining rows (SL3, SL4)

* Reality (SL3) is a.e. throughout — no "continuous + a.e.-equal ⇒ equal" is needed,
  because the datum equation (SL4c) is an integral identity.  Take `ψ i` as the real
  part of `φᵢ` (real Schwartz via `SchwartzMap.postcompCLM Complex.reCLM`); linearity
  of `angularFourier` plus `angularFourier (conj φ) ξ = conj (angularFourier φ (-ξ))`
  (from `fourier_conjugate`, `RealSobolev.lean:61`) and the a.e. conjugate-reflection
  of `g i` (pattern `Annular.lean:200-207`) give `angularFourier ↑(ψℂ i) =ᵐ Gᵢ`.
* The `SchwartzMap → 𝓢'` pairing for SL4a is used as a `change` at `AFD:111`
  (`(f : 𝓢') χ = ∫ x, χ x • ↑f x`); locate the named coercion apply lemma before
  writing SL4a.
