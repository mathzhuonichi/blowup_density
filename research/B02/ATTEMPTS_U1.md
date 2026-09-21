# B02 unit 1 (`annular_truncation`) — attempts and lessons

Task: prove the two spec fields `annularRestriction` and `annularSmoothing` of
`research/B02/Spec.lean` (`Spec.lean:302-318`).

Module: `formalization/NSFormalization/Section4/B02/Annular.lean`
(namespace `NSFormalization.Section4.B02`), building clean, sorry-free,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## What was proved

* `annularRestriction` (`Annular.lean:225`): every datum `A : RealVectorSobolev s`
  is `L²`-approximated by its restriction `Z` to a compact annulus `δ ≤ ‖ξ‖ ≤ R`
  with `0 < δ`.  `Z` is built componentwise as the subtype element
  `⟨(indicator of the open annulus applied to A i).toLp, membership⟩`; membership
  in `realSubspace s` is `annularTruncLp_mem`.
* `annularSmoothing` (`Annular.lean:316`): a datum supported a.e. in the open
  annulus is `L²`-approximated by a smooth one supported in `[δ/2, 2R]`.

## Mathematical structure (both are genuinely new; nothing in-tree does this)

* **`annularRestriction`**: the tail error `eLpNorm ((annulus)ᶜ.indicator (A i)) 2`
  → 0 as `δ = (n+2)⁻¹ → 0`, `R = n+2 → ∞`.  Proved by dominated convergence for
  `∫⁻ (annulusᶜ).indicator ‖A i‖ₑ²`: the sets shrink to `{0}` (null), the integrand
  is dominated by `‖A i‖ₑ²` (finite since `A i ∈ L²`), so
  `tendsto_lintegral_of_dominated_convergence'` gives `→ 0`, transported to
  `eLpNorm` via `ENNReal.continuous_rpow_const` / `Filter.Tendsto.ennrpow_const`
  (`tendsto_eLpNorm_annulus_compl`, `Annular.lean:138`).  Reality: the open
  annulus is `ξ ↦ -ξ` invariant (`neg_mem_frequencyAnnulus`) and its indicator
  real, so the truncation commutes with `Source.RealSobolev.realSymmetry`
  (`RS:27 realSymmetry_ae`, `RS:123 mem_realSubspace_iff`).
* **`annularSmoothing`**: `MemLp.exist_eLpNorm_sub_le` (Mathlib `MSA`) gives a smooth
  compactly supported `g₀ i` with `‖Z i - g₀ i‖₂ ≤ ε/4`.  Multiplying by a real
  annular cutoff `annularCutoff δ R = cutoff R · (1 - cutoff (δ/2))` (built from the
  vendor bump `NavierStokesR3.ComparisonCutoffs.cutoff`), which is `1` on `[δ,R]`
  and supported in `(δ/2, 2R)`, does not increase the `L²` error (`0 ≤ χ ≤ 1` and
  `χ = 1` where `Z i ≠ 0`).  Reality is restored by `Paper3.realProjectionTo`,
  whose coeFn `(1/2)(v(ξ) + conj(v(-ξ)))` is the smooth compactly-supported
  representative demanded by `IsAnnularDatum`, and whose operator norm ≤ 1 keeps
  the estimate.

## Reused declarations

`Paper3.realProjectionTo` / `realProjectionTo_norm_le` / `realProjectionTo_inclusion`
(`RealPositiveDensity.lean`); `Source.RealSobolev.realSymmetry_ae`, `realProjection_apply`,
`mem_realSubspace_iff`, `FourierData`; `NavierStokesR3.ComparisonCutoffs.cutoff` and
its `cutoff_smooth/nonneg/le_one/eq_one/eq_zero`; Mathlib `MemLp.exist_eLpNorm_sub_le`,
`MemLp.indicator`, `tendsto_lintegral_of_dominated_convergence'`,
`eLpNorm_indicator_eq_eLpNorm_restrict`, `eLpNorm_mono_ae`, `PiLp.norm_eq_of_L2`.

## Failed / corrected approaches (kept so they are not re-tried)

1. `MemLp.exists_eLpNorm_indicator_compl_lt` (Mathlib tightness) gives an *arbitrary*
   finite-measure set, **not** an annulus, so it cannot produce
   `IsAnnularRestriction`.  Had to run dominated convergence on the explicit
   annulus sequence instead.
2. The general `Lp` dominated-convergence `tendsto_Lp_of_tendsto_ae` needs
   `UnifIntegrable`/`UnifTight` side-conditions; cheaper to go through
   `∫⁻`-DCT and lift with `ennrpow_const`.
3. `AddSubgroupClass.coe_sub` does **not** apply to `↥(realSubspace s)` (no
   `AddSubgroupClass (ClosedSubmodule …)` instance); the coercion facts
   `((x - y : RealSobolevHilbert s) : FourierData) = ↑x - ↑y` and
   `‖x - y‖ = ‖↑x - ↑y‖` are both `rfl` — use `rfl`.
4. `positivity` was used on a `1 ≤ (n:ℝ)+2` goal — not a positivity goal; use
   `linarith [Nat.cast_nonneg n]`.  `δ = (n+2)⁻¹ < n+2` via `inv_le_one_of_one_le₀`.
5. `Set.not_mem_compl_iff` does not exist; used `not_not.mpr` (defeq to `∉ sᶜ`).
6. `annularCutoff_eq_one` / `annularCutoff_support` need the `0 < δ` hypothesis
   (for `0 < δ/2` inside `cutoff_eq_one/zero`); dropping it broke `positivity`.
7. The `∫⁻ a, sᶜ.indicator h a` form from the DCT does not unify with the
   `∫⁻ a in sᶜ, h a` form; bridge with `lintegral_indicator` before `simpa`.
8. When rewriting `realProjection`'s coeFn, `Pi.smul_apply` / `Pi.add_apply` must
   be interleaved between the `Lp.coeFn_smul` / `Lp.coeFn_add` rewrites, else the
   `((1/2) • ⇑…) ξ` term is not in the `⇑… ξ` shape the next lemma expects.
9. `enorm_sub_lt_of_forall_le` concludes `< ENNReal.ofReal ε`; the goal is `< η`,
   so chain with `lt_of_lt_of_le · hεη` where `ofReal ε ≤ η` (`exists_real_le_enorm`,
   handling `η = ⊤`).

## Commands

From `verification/` after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`:

* `lake build NSFormalization.Section4.B02.Annular` → `Build completed successfully
  (8809 jobs)`, no warnings from `Annular.lean`.
* `lake env lean ../research/B02/axioms_u1.lean` → both examples type-check;
  `#print axioms` on both theorems = `[propext, Classical.choice, Quot.sound]`.
