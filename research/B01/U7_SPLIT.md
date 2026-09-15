# B01 unit 7 — split of `temporalApprox` / `SeparatedTemporalDense`

Target (`research/B01/COMPARISON.md:151`, row 7, rated **L**): for every real `s`
and every `q ∈ [1,∞)` (`1 ≤ q`, `q ≠ ⊤`), finite separated sums
`Σ_{j<J} φ_j(t) • A_j` with `φ_j ∈ C_c^∞`, `tsupport φ_j ⊆ Ioi 0`, and arbitrary
spatial data `A_j : RealVectorSobolev s`, are dense in the datum-path Bochner
space `L^q(0,∞;H^s)` measured by `bochnerDatumENorm`.  Spec objects:
`SeparatedTemporalDense` (`Spec.lean:382`) and the field `temporalApprox`
(`Spec.lean:273`).

**All sub-steps below are closed.** Everything is in
`formalization/NSFormalization/Section4/B01/Temporal.lean`, namespace
`NSFormalization.Section4.B01`; conformance in `research/B01/axioms_u7.lean`.
`#print axioms` on every theorem = `[propext, Classical.choice, Quot.sound]`.

| # | Sub-lemma (Lean-ready statement) | Size | Status / blocker |
|---|---|---|---|
| 1 | **Instantiation.** `dense_span_separatedLp (H := RealVectorSobolev s) (μ := forceTimeMeasure) q hqt (D := Set.univ) dense_univ hdtf : Dense (Submodule.span ℝ {v \| ∃ h ∈ univ, ∃ g ∈ 𝒯, v = separatedLp q h g})`, where `hdtf : Dense 𝒯` and `𝒯` is `dense_positive_temporal_factors q hqt` **retyped at `forceTimeMeasure`**. | S | **Closed** (inline `hdense`). Blocker (resolved): passing the `positiveTimeMeasure`-typed factor set directly makes the generator set mixed-measure and `whnf` loops; retype `𝒯` at `forceTimeMeasure` once (defeq) so the set is uniform. |
| 2 | **`lp_coeFn_finsetSum`** `(t : Finset ι) (F : ι → Lp H p μ) : ⇑(∑ i∈t, F i) =ᵐ[μ] fun x => ∑ i∈t, (F i) x`. | S | **Closed** (standalone theorem). Mathlib has `lp.coeFn_sum` only for the sequence space; proved by `Finset.induction` with `Lp.coeFn_zero`/`Lp.coeFn_add`. |
| 3 | **Span-unwrap + per-index extraction** (`key`+`choose`). `Submodule.mem_span_set'.mp` gives `n`, `f : Fin n → ℝ`, `g : Fin n → ↥Gen`, `∑ f i • ↑(g i) = y`; then for each `i`, coefficient `hcoef i : RealVectorSobolev s`, smooth compact positive-time `afn i`, and `↑(g i) =ᵐ fun t => afn i t • hcoef i` (via `separatedLp_ae`). | M | **Closed.** Blocker (resolved): destructuring `(g i).2` by `obtain` `whnf`-reduces the heavy `separatedLp`/`RealVectorSobolev` membership predicate and exceeds default heartbeats; `simp only [Set.mem_ofPred_eq] at hmem` reduces it by a cheap rewrite instead. `set_option maxHeartbeats 1000000`. |
| 4 | **Separated-shape bookkeeping.** With `φ i := f i • afn i`: `ContDiff ℝ ∞ (φ i)` (`ContDiff.const_smul`), `HasCompactSupport (φ i)` (`HasCompactSupport.smul_left`), `tsupport (φ i) ⊆ Ioi 0` (`tsupport_smul_subset_right` ∘ `hsupp`). A scalar multiple of a positive-time factor is a positive-time factor. | S | **Closed.** |
| 5 | **Raw-path identity** (`hFi`+`hyae`). `⇑y =ᵐ separatedPath φ hcoef`, i.e. `∑_i f i • (afn i t • hcoef i) = ∑_i (f i • afn i t) • hcoef i` pointwise a.e., using sub-lemma 2, `Lp.coeFn_smul`, `separatedLp_ae`, `ae_all_iff`, `smul_smul`. | M | **Closed.** |
| 6 | **`Lp`-quotient → `bochnerDatumENorm`** (`hdiff`+`hval`+bound). `separatedPath φ A - b =ᵐ ⇑(y - B)` (`EventuallyEq.sub`/`Lp.coeFn_sub`, `B := hb.toLp b`), so `bochnerDatumENorm q s (separatedPath φ A - b) = ‖y-B‖ₑ = ENNReal.ofReal ‖y-B‖` (`eLpNorm_congr_ae`, `Lp.enorm_def`, `ofReal_norm`); then `< ENNReal.ofReal ε ≤ η` from `dist B y < ε`, choosing `ε := if η = ⊤ then 1 else η.toReal`. | S | **Closed.** |
| — | **Assembly.** `separatedTemporalDense (q) (hq1 : 1 ≤ q) (hqt : q ≠ ⊤) (s) …` = the `SeparatedTemporalDense q s` body; `temporalApprox : ∀ q, 1 ≤ q → q ≠ ⊤ → ∀ s, …` = the field, `:= fun … => separatedTemporalDense …`. | M | **Closed.** Conformance `axioms_u7.lean` discharges both spec objects by defeq. |

## Route confirmed vs. COMPARISON row 7

The template `SBD:69 dense_span_physical_separated_sobolev` carries the shape:
substituting `PTD:73 dense_positive_temporal_factors` for its spatial-factor
density gives the density (sub-lemma 1).  The remaining work — the *span
unwrapping* into `separatedPath` on **raw paths** and the *`Lp`-quotient → raw
representative* step — is exactly sub-lemmas 2–6, all elementary and now closed.
The one non-obvious cost was that both the mixed-measure generator set and the
`obtain`-destructure of the membership predicate trigger runaway `whnf`; both are
avoided (uniform-measure retype; `simp only [Set.mem_ofPred_eq]`), leaving a
single `maxHeartbeats 1000000` bump for the still-heavy reduction.

## No open gap for unit 7.

`separatedTemporalDense` and the `temporalApprox` field are fully proved with the
standard three axioms and no `sorry`.
