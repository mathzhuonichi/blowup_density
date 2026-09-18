# T22 U-A2 — attempts / pin notes (`Section3/T22/CutoffKernel.lean`)

Lane 391, 2026-09-18. Target: `integrable_weighted_fourier_cutoff` — the Fourier
transform of a smooth compact cutoff is weighted-`L¹` for every polynomial weight.

## Design decision (what worked)

Route everything through one **Schwartz-space** lemma
`integrable_weighted_schwartz (s) (ψ) : Integrable (fun ζ => (1+‖ζ‖²)^(|s|/2) · ‖ψ ζ‖)`
and then apply it to two Schwartz representatives of the cutoff transform that
differ only by the normalized dilation `schwartzAngularDilation`:

- Mathlib `𝓕` version: apply to `ψ := 𝓕 (cutoffSchwartz …)` (a `SchwartzMap`, via
  the `Fourier` instance on `SchwartzMap`), coercion `𝓕 (fun x => (χ x : ℂ))`.
- datum-layer angular version: apply to
  `ψ := schwartzAngularDilation (𝓕 (cutoffSchwartz …))`, whose coercion is exactly
  `angularFourier (fun x => (χ x : ℂ))` by the `rfl` lemma
  `Paper3.schwartzAngularDilation_fourier_apply`.

This avoids proving the change-of-variables (dilation) integrability transfer by
hand: both conventions are Schwartz functions, and the single decay lemma serves
both. It also reuses `NavierStokesR3.CompactSchwartz.ofCompactSupport`
(vendor) so no Schwartz seminorm finiteness has to be re-established.

Analytic core of the master lemma:
- Schwartz decay `SchwartzMap.one_add_le_sup_seminorm_apply` at `k := N`, `n := 0`,
  `m := (N, 0)` gives `(1+‖ζ‖)^N · ‖iteratedFDeriv ℝ 0 ψ ζ‖ ≤ 2^N · sup(seminorms) ψ`;
  `norm_iteratedFDeriv_zero` turns `‖iteratedFDeriv 0‖` into `‖ψ ζ‖`.
- weight comparison `(1+‖ζ‖²)^(|s|/2) ≤ (1+‖ζ‖)^|s|` from `1+‖ζ‖² ≤ (1+‖ζ‖)²` and
  `Real.rpow_le_rpow` + `← Real.rpow_natCast`/`← Real.rpow_mul` (exponent `2·(|s|/2)=|s|`).
- pick a natural `N > |s| + 3` (`exists_nat_gt`), dominate by
  `C_N·(1+‖ζ‖)^(-(N-|s|))`, integrate with `MeasureTheory.integrable_one_add_norm`
  since `finrank ℝ Space = 3 < N - |s|` (`by simp [Space]`).
- `Integrable.mono'` with a `Continuous.aestronglyMeasurable` integrand.

## Statement spelling (important for U-A3)

The brief's literal `Integrable (fun ζ => (1+‖ζ‖²)^(|s|/2) * ‖𝓕χ ζ‖)` with
`χ : Space → ℝ` does **not** typecheck: Mathlib's `𝓕` needs a codomain that is a
`NormedSpace ℂ`, and `ℝ` is not. The honest statement takes the transform of the
complex coercion `fun x => (χ x : ℂ)`, which is also exactly the multiplier
`IsCutoffDatum` uses (`SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ))`,
`Spec.lean:118-128`). The primary theorem is stated for the datum-layer
`angularFourier`; the Mathlib `𝓕` variant is provided alongside.

## Pin notes (v4.34.0-rc2 + this Mathlib)

- `le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b` — the plain `le_div_iff` is
  gone; used to turn `b^N · ‖ψ ζ‖ ≤ C` into `‖ψ ζ‖ ≤ C · b^(-N)`.
- `Real.rpow_neg`, `Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_mul`
  (`hx : 0 ≤ x`) for moving between `(·)^(n:ℕ)` and `(·)^(r:ℝ)` and combining
  exponents; `Real.rpow_le_rpow` / `Real.rpow_nonneg` for monotonicity/sign.
- `norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0 f x‖ = ‖f x‖`.
- `HasCompactSupport.comp_left (hf) (hg : g 0 = 0) : HasCompactSupport (g ∘ f)`
  (the additive `to_additive` of the `HasCompactMulSupport` version); here
  `g := Complex.ofReal`, `hg := Complex.ofReal_zero`.
- `Complex.ofRealCLM.contDiff.comp hχ` gives `ContDiff ℝ ∞ (fun x => (χ x : ℂ))`.
- `SchwartzMap.fourier_coe (f) : ⇑(𝓕 f) = 𝓕 ⇑f := rfl` and
  `Paper3.schwartzAngularDilation_fourier_apply (φ) (ξ) :
   schwartzAngularDilation (𝓕 φ) ξ = angularFourier ⇑φ ξ := rfl` — both `rfl`, so
  the two wrappers close by `Integrable.congr` + a trivial `rfl` on the integrand.
- `hasFiniteIntegral_iff_ofReal (h : 0 ≤ᵐ f)` rewrites `HasFiniteIntegral` to
  `∫⁻ ofReal (f ·) < ⊤`, giving the `ENNReal` corollary.

## Reuse

- `NavierStokesR3.CompactSchwartz.ofCompactSupport` (vendor) — smooth compact ⇒ `SchwartzMap`.
- `NSFormalization.Paper3.schwartzAngularDilation` / `schwartzAngularDilation_fourier_apply`
  (`Paper3/AngularFourierDilation.lean`) — the `SchwartzMap`-level angular transform.
- `NSFormalization.Source.angularFourier` — the manuscript's angular convention (datum layer).
- Cross-check: `Paper3/CompactFourier.lean` (`compact_fourier_bessel_integrable`) does
  the same weighted `L²` argument (`‖𝓕 f ζ‖²`); U-A2 needs the `L¹` version (`‖𝓕χ ζ‖`).

## Failed / discarded routes

- Stating the goal directly for `𝓕χ` with `χ : Space → ℝ` — type error (no
  `NormedSpace ℂ ℝ`). Resolved by the complex coercion (above).
- Proving the angular version by a change-of-variables integrability transfer
  from the Mathlib version — unnecessary once the angular transform is recognized
  as another `SchwartzMap` (`schwartzAngularDilation (𝓕 ·)`) and the master lemma
  applied to it directly.
