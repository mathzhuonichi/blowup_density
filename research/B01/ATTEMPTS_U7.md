# B01 unit 7 — attempts log (`temporalApprox` / `SeparatedTemporalDense`)

Module: `formalization/NSFormalization/Section4/B01/Temporal.lean`.
Conformance: `research/B01/axioms_u7.lean`.

## What worked (final proof)

`dense_span_separatedLp` (SBD:30) at `H := RealVectorSobolev s`,
`μ := forceTimeMeasure`, `D := univ`, time set `dense_positive_temporal_factors`
(PTD:73); `Submodule.mem_span_set'` to a `Fin n` combination; `φ i := f i • afn i`
where `afn i` is the smooth representative of the `i`-th time factor; then the
`Lp.coeFn_*` / `eLpNorm_congr_ae` / `Lp.enorm_def` / `ofReal_norm` bookkeeping.
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Failed / costly approaches and the fix

1. **`whnf` timeout destructuring `(g i).2` with `obtain`.**  `(g i).2` is
   membership in the separated-span generator set, whose predicate contains the
   `separatedLp` CLM (`compLpL₂`) and the heavy `RealVectorSobolev`/Fourier
   carriers.  `obtain ⟨…⟩ := (g i).2` forces `whnf` of that predicate and blows
   the default 200 000 heartbeats; the *deep* pattern (also reducing
   `gg ∈ 𝒯`) needs > 1 000 000.  **Fix:** `have hmem := (g i).2;
   simp only [Set.mem_ofPred_eq] at hmem` reduces the membership to its
   existential normal form by a cheap *rewrite* (not `whnf`); the deep destructure
   of `hmem` then fits well under `maxHeartbeats 1000000`.  (`Set.mem_setOf_eq`
   works too but is deprecated in favour of `Set.mem_ofPred_eq`.)

2. **Mixed-measure generator set.**  Passing `dense_positive_temporal_factors q hqt`
   (typed at `positiveTimeMeasure`) directly as `hA` while forcing
   `μ := forceTimeMeasure` on the `H` side produces a generator set whose
   scalar factor lives at `positiveTimeMeasure` and whose product lives at
   `forceTimeMeasure`.  Even at 4 000 000 heartbeats the mixed-measure
   destructure was slow/looping.  **Fix:** retype the factor set once,
   `have hdtf : Dense {v : Lp ℝ q forceTimeMeasure | …} := dense_positive_temporal_factors q hqt`
   (defeq, since `forceTimeMeasure` unfolds to `positiveTimeMeasure`), so the
   whole generator set is uniform in the measure.

3. **`set_option maxHeartbeats N in` placed after the docstring.**  Writing
   `/-- … -/` then `set_option … in` then `theorem` is a parse error
   (`unexpected token 'set_option'; expected 'lemma'`) and silently leaves the
   default limit.  **Fix:** `set_option … in` must come *before* the docstring.

4. **Pointwise `rw` chain in `hdiff` fighting `set B`.**  `set B := hb'.toLp b`
   makes `B` opaque; a later `hb'.coeFn_toLp` mentions `MemLp.toLp b hb'`, not
   `B`, so `rw [hsub, Pi.sub_apply, hy, hB]` failed to find `↑↑y t` /
   `↑↑(MemLp.toLp b hb') t` against a goal still showing `↑↑B`.  **Fix:** phrase
   the coeFn fact on `B` (`have hBcoe : ⇑B =ᵐ b := hb'.coeFn_toLp`, defeq) and
   assemble the difference with the `EventuallyEq` combinators
   `(hyae.symm.sub hBcoe.symm).trans (Lp.coeFn_sub y B).symm` — no pointwise
   rewriting, no `Pi.sub_apply`.

5. **`lp_coeFn_finsetSum` empty case.**  `simp` alone left
   `↑0 =ᵐ[μ] fun x => 0`.  **Fix:** `simp only [Finset.sum_empty]` then
   `exact Lp.coeFn_zero (E := H) (p := p) (μ := μ)`.

## Notes for reuse

* `lp_coeFn_finsetSum` is a general `Lp`-quotient analogue of `lp.coeFn_sum`
  (which Mathlib provides only for the sequence space); reusable by any B01/B02
  finite-Bochner-sum step.
* Sub-lemma 1's uniform-measure retype pattern is the template for B02, which
  shares stage 4 verbatim (`COMPARISON.md:169-183`).


## Review fixes (lead, 2026-09-13)

- Heartbeats lowered from `1000000` to `400000` (reviewer bisection: floor 375,034; Mathlib `#count_heartbeats` suggests 400000). The bump is needed, but the cost sits in `hval` (the `bochnerDatumENorm` unfolding over `RealVectorSobolev`, ~50%) and `hFi` (~25%), **not** in the span-membership destructure as §1 says; that step costs ~11% and would not by itself require a bump.
- `separatedTemporalDense` is proved under the field's own guards `1 ≤ q → q ≠ ⊤` (the manuscript's `1 ≤ q < ∞`), not for all `q`.
