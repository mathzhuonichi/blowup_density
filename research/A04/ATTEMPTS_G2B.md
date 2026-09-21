# A04 unit G2b — `highContinuationIntegral` (lane 138)

Target: spec field `research/A04/Spec.lean:471-494` `highContinuationIntegral`,
the `ζ↓0` integrated form of eq:highcontinuation, token-for-token.
Deliverable module `formalization/NSFormalization/Section4/A04/HighContinuationIntegral.lean`,
theorem `NSFormalization.Section4.A04.highContinuationIntegral`.

**Result: proved, first compiling attempt.** Std axioms
`[propext, Classical.choice, Quot.sound]`. The recipe in `G1_SPLIT.md` §G2b was
exact; no failed *approach* had to be abandoned, but three concrete traps were
anticipated and designed around, recorded here.

## Route (as built)

`refine ⟨_, _⟩`:

* **Conjunct 1 (`IntervalIntegrable`)** =
  `intervalIntegrable_highContinuationIntegrand hf w A04.Cgron m ht₀ htt htT`
  (`Continuity.lean:132`), one application. `A04.Cgron` passed **explicitly**
  because that theorem carries a `Cgron : ℕ → ℝ → ℝ` *parameter* that shadows the
  def; the value is supplied at the call site (no local binder there, so plain
  `Cgron` would also have resolved, but `A04.Cgron` matches the recipe).

* **Conjunct 2 (the bound)** = `sqrt_le_primitive_linear` (`Regularized.lean:134`)
  at `E := fun r => sobolevNormAt (m:ℝ) w.velocity r ^ 2`,
  `E' := fun s => deriv E s`, `K := fun s => Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2`,
  `b := fun s => sobolevNormAt (m:ℝ) f s`, applied at the upper endpoint
  `t ⟨htt, le_rfl⟩ : t ∈ Icc t₀ t`, then converted to the spec spelling by a
  three-line `calc` with `Real.sqrt_sq`.

## Load-bearing hypotheses / lemmas

* `deriv_normSq_absorbed` (`HighContinuation.lean:131`) — supplies both the
  interior `HasDerivAt E (deriv E s) s` (`hdE`, via `⟨d, hd, -⟩` then
  `rw [hd.deriv]; exact hd`) and, doubled through
  `deriv_normSq_absorbed_deriv` (`:150`), the `hineq`
  `deriv E s ≤ 2·(K·E + b·√E)`. Needs `s ∈ Ioo 0 T`, obtained from
  `s ∈ Ioo t₀ t` by `⟨lt_of_le_of_lt ht₀ hs.1, lt_trans hs.2 htT⟩` (the
  `0 ≤ t₀` and `t < T` hypotheses are exactly what makes `Ioo t₀ t ⊆ Ioo 0 T`).
* `continuousOn_sobolevNormAt_velocity` / `_force` (`Continuity.lean:105,114`)
  mono'd along `hsub : Icc t₀ t ⊆ Ico 0 T`; `.pow 2` for `E` and for the `H²`
  factor of `K`; `continuousOn_const.mul …` for `K`. Unit N1; uses only the
  `ContinuousOn` datum path, **not** `HasSmoothSobolevPath`.
* `Real.sqrt_sq (h : 0 ≤ x) : √(x^2) = x` (`Mathlib/Analysis/Real/Sqrt.lean:181`),
  with `0 ≤ sobolevNormAt … = ENNReal.toReal_nonneg` (it is a `.toReal`). Used in
  `hineq` (turns `√(‖u‖²) → ‖u‖`), and at both integral endpoints + inside the
  integrand in the closing `calc`.
* `MemL1Hm f` (`_hf1`) is **unused** by the proof, present only for spec fidelity
  (it books the `L¹_tH^m` bound of the forcing integral). Named `_hf1` to keep the
  unused-variable linter quiet.

## Traps designed around (would have been errors)

1. **`hbnonneg` is the FORCE norm, not the velocity norm.** `sqrt_le_primitive_linear`'s
   `hbnonneg : ∀ s ∈ Ioo t₀ t, 0 ≤ b s` needs `0 ≤ sobolevNormAt (m:ℝ) f s`. The
   velocity nonnegativity `hvnn s : 0 ≤ sobolevNormAt (m:ℝ) w.velocity s` is the
   *wrong* term; supplying `fun s _ => hvnn s` would type-mismatch. Correct:
   `fun s _ => ENNReal.toReal_nonneg` (bare, `b s` is itself a `.toReal`).

2. **`rw … at hmain` under the integral binder would fail on un-β-reduced applied
   lambdas.** `sqrt_le_primitive_linear`'s conclusion is
   `√(E t) ≤ √(E t₀) + ∫ s, (K s · √(E s) + b s)`; after substituting the four
   lambdas, `hmain`'s stored type carries `√((fun r => …) t)` and
   `(fun s => …) s` applications that are defeq — but not syntactically —
   `√(sobolevNormAt … t ^ 2)` etc., so a direct `rw [Real.sqrt_sq (hvnn t)] at hmain`
   can miss. **Design:** never `rw at hmain`. Instead a `calc` whose middle step
   `_ ≤ <β-reduced RHS> := hmain` uses **defeq** (which handles β) to accept
   `hmain`, and the endpoint / integrand `Real.sqrt_sq` rewrites happen on the
   freshly-written β-reduced forms in the `calc` lines and in `hintEq`.

3. **The integrand rewrite must go through `intervalIntegral.integral_congr`**, not
   `rw` under the binder. `hintEq`'s LHS is written verbatim as the β-reduced
   `hmain` integrand, so `rw [hintEq]` in the final `calc` step matches
   syntactically; the pointwise goal is closed by `rw [Real.sqrt_sq (hvnn s)]`
   (associativity already agrees: `K s * √E = Cgron m ν * ‖u‖²_{H²} * ‖u‖_{H^m}`).

## `hineq`/atoms note

`hineq` closes with `linarith [habs]` where
`habs := deriv_normSq_absorbed_deriv …`: goal `deriv E s ≤ 2·(P + Q)`, `habs`
`(1/2)·deriv E s ≤ P + Q` with the two products `P,Q` **syntactically identical**
across goal and `habs` (both left-assoc), so `linarith` treats them as one atom
and only the ×2 is linear work. No `nlinarith` needed.

## The `t₀ = t` degenerate case

Not special-cased: `sqrt_le_primitive_linear` takes `t₀ ≤ t₁` (equality allowed);
`Ioo t₀ t = ∅` makes `hdE`, `hineq`, `hKnonneg`, `hbnonneg` vacuous and the
antitone-on-a-point argument trivial. `hsub` still holds because `t₀ ≤ t < T`.

## Commands

```
cd verification && lake build NSFormalization.Section4.A04.HighContinuationIntegral   # ✔ Built (3.7s)
cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/HighContinuationIntegral.lean  # silent
cd verification && lake env lean ../research/A04/axioms_high_continuation_integral.lean
#   → 'NSFormalization.Section4.A04.highContinuationIntegral' depends on axioms:
#     [propext, Classical.choice, Quot.sound]   (+ conformance example elaborates)
make check   # architecture + contract policy + work-queue: all OK
```

No zero-solution instantiation: no `ClassicalSolutionR` zero witness exists in
the tree (grep of `research/A04`, `Section4/A04` for `zero.*[Ss]olution` empty),
so the "if cheap" instantiation is skipped.

## Review follow-up (REVIEW_G2B.md, applied by the lead as records only)

- Trap 2 was **not real**: the reviewer's `trace_state` shows `hmain` enters the context fully β-reduced, so `rw … at hmain` succeeds and the naive three-line route compiles (`t2c.lean`). The `calc` route is fine but not forced; not a lesson.
- Consumers of `regularizedNormDerivative` (G2): **none** tree-wide — G2b goes through `deriv_normSq_absorbed` + `sqrt_le_primitive_linear` and bypasses it. The G1_SPLIT note claiming a consumer exists is corrected below. For the A04 V2 contract: register `regularizedNormDerivative` anyway (manuscript display, proved, zero marginal cost) but disclose in scope that it and `highContinuationIntegral` are parallel manuscript statements, the latter not routed through the former, and that it currently has no consumer.
- `MemL1Hm f` is not only unused but derivable (`memL1Hm_of_memForceR`); kept for rule-2 fidelity, to be disclosed in the V2 scope.
- A zero-solution witness has been rebuilt in four review appendices of this node; MAINT should land it once (e.g. `Section4/A04/ZeroSolution.lean`).
- V2 recipe from the review: `Contracts/V2/EnergyHighPartial.lean` importing only `Contracts.V1.EnergyHighPartial`; one new restatement `MemL1Hm` with a fourth `rfl` bridge; `Cgron` opaque + `Cgron_pos`, value `(Chigh m)²/(4ν)` only as a binding-level `rfl` bonus; ten scope disclosures (notably `Cgron` junk `0` at `ν = 0`, so `0 < ν` cannot weaken; integrated not differential; `IntervalIntegrable` asserted; `.toReal` touches only the velocity and force slots — do not copy V1's gradient-slot sentence; endpoints include `t₀ = 0`; conditional on `HasSmoothSobolevPath`).
