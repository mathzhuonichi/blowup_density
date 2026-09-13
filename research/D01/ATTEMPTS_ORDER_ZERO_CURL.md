# SL7b-β — order-0 longitudinal (curl-free) Fourier identity (lane 108)

Module: `formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean`
Axiom audit: `research/D01/axioms_order_zero_curl.lean` (all 14 public decls =
`propext, Classical.choice, Quot.sound`).

## What is proved (Lemma B)

`orderZeroDatum_longitudinal_of_curl_free (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
   (hcurl : ∀ i j x, partialDeriv i z x j = partialDeriv j z x i) :
   ∀ᵐ ξ, ∀ i j, (ξ i : ℂ) * (orderZeroDatum hz j : FourierData) ξ
              = (ξ j : ℂ) * (orderZeroDatum hz i : FourierData) ξ`

i.e. the order-0 angular Sobolev datum of a **curl-free** smooth `L²` field is a.e. **longitudinal**,
with the *same statement shape* as lane 089's `longitudinal_of_curl_free`, but seeded at order 0
from `MemLp 2` + smoothness only. **No integrability of the derivatives is used.** Corollary
`Leray.lerayComplement_zero_orderZeroDatum_eq_self : lerayComplement 0 (orderZeroDatum hz) =
orderZeroDatum hz` via lane 089's `Leray.lerayComplement_eq_self_of_longitudinal 0`.

This is the longitudinal companion to lane 094's transverse Lemma A, and (with 094) supplies both
halves of the order-0 `eq:Rpressure` decomposition.

## Route as executed (the review's "weight-matrix" factoring, done as step 1 not after-the-fact)

The divergence case (094) and the curl case share ONE cutoff/DCT machine, written once here as a
constant weight-matrix pairing:

1. **`Cut.physical_weighted_pairing_zero`** (the analytic heart, generalizing 094's
   `Cut.physical_pairing_zero`). For a smooth `L²` field and any constant matrix `w : Fin 3 → Fin 3
   → ℂ` with `∑ᵢⱼ w i j (∂ᵢ z_j x) = 0` pointwise, `∑ᵢⱼ w i j ∫ (∂ᵢψ) z_j = 0` for every Schwartz
   `ψ`. Proved by the same `χ(·/R)` cutoff limit as 094: per-`(i,j)` Leibniz split
   `∂ᵢ(χ_R ψ) = χ_R ∂ᵢψ + ψ ∂ᵢχ_R`, the compactly-supported weighted pairing
   `Cut.cs_weighted_pairing_zero` gives `∑ᵢⱼ w i j ∫ ∂ᵢ(χ_R ψ) z_j = 0` for every `R`, the B-part
   → `∑ᵢⱼ w i j ∫ (∂ᵢψ) z_j` by dominated convergence (`|χ_R| ≤ 1`, `χ_R → 1`), and the A-part → 0
   because `‖∇χ_R‖ ≤ C/R` (094's `Cut.chi_deriv_bound`) times a fixed `L¹` mass. The per-index
   DCT/boundary limits are index-independent; only the finite weighted sum changed vs 094.
   `w = δ` recovers 094's divergence case (SIMP lane can re-derive it); `w = Cut.wAnti p q` (the
   antisymmetric `w p q = 1, w q p = -1`) gives the curl case.
2. **`Cut.physical_antisym_pairing_zero`.** The `w = wAnti p q` instance:
   `∫ (∂ₚψ) z_q = ∫ (∂_qψ) z_p`. The pointwise hypothesis `∂ₚ z_q − ∂_q z_p = 0` is `hcurl`.
3. **`tempered_antisym_eq`.** Hence `∂ₚ(z_q : 𝓢') = ∂_q(z_p : 𝓢')` as tempered distributions
   (equality form, so `map_neg` + `sub_eq_zero` close it; no distribution-subtraction `sub_apply`
   needed). Uses `TemperedDistribution.lineDerivOp_apply_apply`, `Lp.toTemperedDistribution_apply`.
4. **`fourier_antisym`.** Distributional Fourier: `congrArg fourierCLM` on the equality, tested
   against `ψ` and combined with the single-component symbol identity `fourier_lineDeriv_apply`
   (094's `fourier_transverse` `hterm`, generalized so direction `d` ≠ component `c`), gives
   `2πi ∫ ξₚ ψ 𝓕z_q = 2πi ∫ ξ_q ψ 𝓕z_p`; cancel `2πi`; then the fundamental lemma
   `ae_eq_zero_of_integral_contDiff_smul_eq_zero` upgrades to `ξₚ 𝓕z_q − ξ_q 𝓕z_p = 0` a.e.
   (`LocallyIntegrable.sub` of the two `hlocterm`-style factors).
5. **`orderZeroDatum_longitudinal_symm`.** Cycles form, from `fourier_antisym` + 094's
   `orderZeroDatum_symm_ae` (order-0 angular weight symbol is `1`), merged over the 9 pairs with
   `ae_all_iff`.
6. **`longitudinal_of_longitudinal_symm`.** The dilation transport to the angular convention.

## Reused (not re-proved)

From lane 094 `OrderZeroSymbol.lean` (all in the *public* `NSFormalization.Section4.D01.Cut`
namespace — nothing was `private`, so reuse is by `open Cut`):
`bump`, `chi`, `chi_smooth`, `chi_cs`, `chi_le1`, `chi_nonneg`, `chi_eventually_one`,
`chi_deriv_bound`, `exists_deriv_bound`, `Pj`, `zc`, `zc_eq`, `hasFDeriv_zc`, `zc_smooth`,
`norm_cv`; and (namespace `...D01`) `componentLp`, `componentLp_ae`, `memLp_component`,
`orderZeroDatum`, `orderZeroDatum_symm_ae`, `angularFrequencyDilation_coeFn`.
From lane 089 `Longitudinal.lean`: `Leray.lerayComplement_eq_self_of_longitudinal`.
Mathlib: `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`, `TemperedDistribution.{lineDerivOp_apply_apply,
fourier_lineDerivOp_eq, smulLeftCLM_apply_apply}`, `Lp.{fourier_toTemperedDistribution_eq,
toTemperedDistribution_apply}`, `ae_eq_zero_of_integral_contDiff_smul_eq_zero`,
`tendsto_integral_of_dominated_convergence`, `squeeze_zero_norm`,
`LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`, `Fintype.sum_prod_type`,
`integral_finsetSum`.

## Re-proved because 094 exposes only the `k = j` diagonal (recorded per the reviewer's §5 plan)

`Cut.fderiv_zc_eq'` and `Cut.cs_ibp` are the two-index versions of 094's `fderiv_zc_eq` (:157) and
of the `hibp` inlined inside 094's `cs_pairing_zero` (:181). 094's file is merged/frozen, so these
are re-derived here from the public `hasFDeriv_zc` / `zc_smooth` (bodies identical to the reviewer's
`/tmp/rev094/lemB.lean` prototype). A SIMP lane could promote them into `OrderZeroSymbol` and shrink
`cs_pairing_zero`.

`longitudinal_of_longitudinal_symm` is the pairwise analogue of 094's `transverse_of_transverse_symm`.
**Checked:** 094's `transverse_of_transverse_symm` is stated ONLY for the divergence sum
`∑ⱼ ξⱼ gⱼ = 0` (a single scalar identity), NOT for a general per-pair symbol identity, so it does not
apply to the longitudinal shape `ξᵢ g_j = ξⱼ g_i`. Its proof body IS reusable verbatim, though: this
lemma's body is a copy of 089's `longitudinal_of_curl_free` §2 transport with the concrete datum
`A : RealVectorSobolev s` replaced by a bare family `g : Fin 3 → FourierData`. **SIMP factoring:**
promote both the transverse `transverse_of_transverse_symm` and this pairwise
`longitudinal_of_longitudinal_symm` (plus 079's `angularFrequencyDilation_coeFn`) to
`Paper3/AngularFourierDilation.lean` and rewrite 079/089/094 to consume them.

## Failed approaches / dead ends (and why)

- **Reusing 094's `physical_pairing_zero` directly for the curl case — impossible.** It bakes in the
  divergence hypothesis `hdiv` (via `cs_pairing_zero hsmooth hdiv` inside its `hcancel`), so it only
  yields `∑ⱼ ∫ (∂ⱼψ) zⱼ = 0`. The curl case needs a different pointwise cancellation; the cutoff
  machine had to be re-run in weighted form. (Confirmed the divergence sum cannot be massaged into
  the antisymmetric pair without a new hypothesis.)
- **Avoiding the sum/integral swap in `cs_weighted_pairing_zero` — not possible.** After IBP the
  integrand `∑ᵢⱼ w i j (φ ∂ᵢz_j)` is pointwise `0` (`φ · 0`), but the LHS is a *sum of integrals*;
  turning it into the *integral of the pointwise-zero sum* needs one `integral_finsetSum`. Flattening
  the double sum to `∑ over Fin 3 × Fin 3` (`Fintype.sum_prod_type`) makes it a single
  `integral_finsetSum` and avoids nested-swap bookkeeping.
- **`sum_wAntisym_mul` sum evaluation:**
  * `fin_cases p <;> fin_cases q <;> simp [Fin.sum_univ_three, Fin.ext_iff] <;> ring` →
    **`simp` maximum recursion depth** (the `Fin.ext_iff` rewrite loops on the 9 `Fin 3` literal
    comparisons). Fix: drop `Fin.ext_iff`; `fin_cases p <;> fin_cases q <;> simp [Fin.sum_univ_three]
    <;> ring` reduces the `if`s by `simp`'s own `Fin` decision and closes.
  * `simp only [... and_false, ite_false ...] <;> abel` → **left `if (True ∧ False)` unreduced**
    (the `∧`/`ite` reductions did not fire under `simp only` after `Fin.reduceEq`); full `simp` is
    needed to decide the conditions.
- **Contracting `wAnti` into `physical_antisym_pairing_zero`'s conclusion — two failures then a fix:**
  * `rw [sum_wAntisym_mul p q (fun i j => ∫ …)] at hmain` (explicit lambda `a`) → **`rewrite` did not
    find the pattern**: providing `a` as an explicit lambda over the integral left a metavariable in
    the `(∂ᵢψ) x` slot, so the LHS pattern `∑ᵢⱼ wAnti * ∫ ?m • z_j` did not match `hmain`.
  * A `calc` step justified by `(sum_wAntisym_mul p q (fun i j => ∫ …)).symm` → **`whnf` heartbeat
    timeout (200000)**: checking `a p q − a q p` defeq the written reduced difference forced Lean to
    `whnf` the integral-valued lambda application, which is expensive.
  * **Fix:** `rw [sum_wAntisym_mul] at hmain` with `a` **left to be inferred** (Miller higher-order
    *pattern* unification against `hmain`'s `∑ᵢⱼ wAnti p q i j * (∫ (∂ᵢψ) z_j)` succeeds), then
    `exact hmain`. No explicit lambda, no beta-defeq `whnf`.
- **`ae_eq_zero_of_integral_contDiff_smul_eq_zero` target shape:** `LocallyIntegrable.sub` gives
  `LocallyIntegrable (F − G)` as a *Pi-level* function subtraction, so the fundamental-lemma
  integrand is `g x • ((F − G) x)`, not `g x • (F x − G x)`. A `rw [show (fun ξ => g ξ • (…)) = …]`
  did not match; fix: `simp only [Pi.sub_apply, smul_sub]` first, then `rw [integral_sub …]`.

## SL7b remainder after this (toward `(I−P) datum⁰(h) = datum⁰(∇p)`, P2 SL7(7b))

With lane 094 (transverse) and lane 108 (this, longitudinal), the order-0 datum-level pieces of the
`eq:Rpressure` decomposition are done. Still assembly-only (no new mathematics), per
`REVIEW_ORDER_ZERO.md` §6:
1. **`orderZeroDatum` additivity** `orderZeroDatum (h₁+h₂) = orderZeroDatum h₁ + orderZeroDatum h₂`
   — not in `OrderZeroDatum.lean`; cheapest via datum uniqueness
   (`angularRealization_injective` + `isSobolevDatum_orderZeroDatum`).
2. **`lerayComplement` linearity** — `LerayDatum.lean:255` `lerayComplement` is a `→L[ℝ]` bundled
   map, so `lerayComplement_add`/`map_add` is a few lines.
3. **`MemLp 2` / `ContDiff ∞` of `∂ₜu(t,·)` and `∇p(t,·)`** (from `A02/SolutionClass` under
   `MemForceR f`, and `ClassicalSolutionR.pressure_gradient`) — the main remaining plumbing.
4. **Curl-freeness of `∇p`** feeding this lemma's `hcurl`: Clairaut / Mathlib second-derivative
   symmetry on the smooth pressure. (Divergence-freeness of `∂ₜu` feeds 094's `hdiv`; lane 074's
   `DivergenceTime.spatialDivergence_temporalDerivative_eq_zero` fills it by `rfl` per the 094
   reviewer.)

## Commands run

```
cd verification && lake build NSFormalization.Section4.D01.OrderZeroCurl
                                                → Build completed successfully (9916 jobs).
cd verification && lake env lean ../formalization/.../OrderZeroCurl.lean → no output, exit 0
cd verification && lake env lean ../research/D01/axioms_order_zero_curl.lean
                                                → 14 decls, all [propext, Classical.choice, Quot.sound]
grep -nE 'sorry|admit|native_decide|maxHeartbeats|set_option|axiom' OrderZeroCurl.lean
                                                → only the :46 docstring prose
make check                                                              → exit 0
```
