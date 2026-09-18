# Lane 348 — `wholeSpace_identity` attempts and lessons

Target: field `wholeSpace_identity` of `research/T13/probes/api_on_canonical.lean:47-51`
(`03-torus.tex:40-51`), shipped as
`NSFormalization.Section3.T13.WholeSpaceIdentity.wholeSpace_identity`.

## Route that worked (COMPARISON item 2)

1. **Infimum bridge** `dotHomogeneousENorm_eq_homogeneousFourierENorm`: for smooth
   compact `f`, `isHomogeneousSliceDatum_compact` gives existence + the constant
   norm value, so the datum-infimum collapses to `homogeneousFourierENorm`.
2. **Angular Plancherel** `lintegral_angularFourier_sq`: for a Schwartz `φ`,
   `∫⁻ ‖angularFourier φ‖² = ∫⁻ ‖φ‖²`.  Derived through
   `schwartzAngularDilation_norm_toLp` (D01/Paper3) +
   `SchwartzMap.toLp_fourier_eq` + `MeasureTheory.Lp.norm_fourier_eq` (Mathlib
   L² Plancherel), bridged to `∫⁻ ofReal ‖·‖²` via `SchwartzMap.norm_toLp` and
   `eLpNorm_eq_lintegral_rpow_enorm_toReal`.
3. **Translation phase** `angularFourier_translate` from `Source.fourier_translate`
   (`𝐞(-⟪x₀,ξ⟫)`), cancelling `2π·frequencyUnit⁻¹ = 1`; plus additivity
   `angularFourier_sub` via `angularFourier_eq_integral` and `integral_sub`.
4. **Kernel scaling** `lintegral_kernel_smul`: rotation
   (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq` +
   `OrthonormalBasis.measurePreserving_repr_symm`) + Haar dilation
   (`Measure.map_addHaar_smul`, `lintegral_map`, `lintegral_smul_measure`),
   constant `r^{3+2s}·r^{-3} = r^{2s}`.  Holds for all `s`; only `ξ ≠ 0` used
   (`ξ = 0` null by `Homogeneous.ae_ne_zero`).
5. **Assembly** `IReal_decomp` (norm² = Σ components, `lintegral_finsetSum` twice)
   → `component_integral_eq` (pull `K` out, per-`h` Plancherel, Tonelli
   `lintegral_lintegral_swap`, kernel scaling) → `homogeneousFourierENorm_sq`.
   Finiteness from `constant_pos_finite` (344) and `homogeneousFourierENorm_lt_top`.

## Failed approaches / traps (negative examples)

- **`fun_prop` bug with a function-typed local**: whenever `f : SpatialField`
  (`= Space → Space`) is in context, `fun_prop` aborts with
  `fun_prop bug: function expected, got f : SpatialField, type ctor const`, even
  for goals not mentioning `f`.  Fix: build every `f`-dependent continuity
  explicitly (`Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp …)`),
  and extract `f`-free measurability into standalone lemmas
  (`continuous_phase`, `measurable_weightedSq`) where `fun_prop` is safe.
- **`whnf` timeout (200k, even 400k) in the decomposition**: deriving the
  per-`x` measurability as `(hJ1 i).comp (measurable_const.prod_mk measurable_id)`
  forced a defeq check `uncurry F (h,x) = F h x` through the `EuclideanSpace`
  `ofLp` coercions and blew up `whnf`.  Fix: prove `hmx` **directly** with
  explicit continuity, never by composing the uncurried joint-measurability.
- **Constant-in-`x` kernel factor**: the `x`-integrand carries `* fractionalRadialKernel s h`
  with `h` fixed, so its measurability is `(…).mul measurable_const`, not
  `.mul hKm` (which typed `Measurable (fractionalRadialKernel s)` and mismatched).
- **No `Measurable.rpow` for real `rpow`**: `Real.measurable_rpow`,
  `Measurable.rpow_const` do not exist under this name; `fun_prop` closes
  `Measurable (fun ξ => ‖ξ‖^(2s) * …)` in an `f`-free context instead.
- **Deprecations at v4.34.0-rc2**: `eLpNorm_eq_lintegral_rpow_enorm` →
  `eLpNorm_eq_lintegral_rpow_enorm_toReal`.
- **`Integrable.bdd_mul`** takes the bound as `{c : ℝ}` implicit +
  `hf_bound : ∀ᵐ x, ‖f x‖ ≤ c` (an `∀ᵐ`, via `Filter.Eventually.of_forall`), not
  an existential `⟨1, …⟩`.
- **Docstring before `set_option … in`**: a `/-- … -/` may not sit between
  `set_option maxHeartbeats 400000 in` and the theorem; put the `set_option`
  first.

## Notes

- `IReal_eq_cFrac_mul_homogeneousFourierENorm_sq` needs
  `set_option maxHeartbeats 400000 in` (large multi-step `ℝ≥0∞` `calc`).
- `exists_rotation` is a `private` helper; audited transitively.
