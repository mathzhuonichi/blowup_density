# A04 unit Z1 — attempts and notes

Module: `formalization/NSFormalization/Section4/A04/Regularized.lean`
(namespace `NSFormalization.Section4.A04`). Axiom audit:
`research/A04/axioms_z1.lean`. All five declarations:
`[propext, Classical.choice, Quot.sound]`. Build: `cd verification && lake build
NSFormalization.Section4.A04.Regularized` (clean, ~1.7 s warm).

## What was proved

1. `regularized_sqrt_bound` — the ζ-regularized bound, **purely algebraic** (no
   differentiability): from `d ≤ 2 (K t · E t + b t · √(E t))` with
   `E t, K t, b t ≥ 0`, `ζ > 0`, get
   `d / (2 √(E t + ζ²)) ≤ K t · √(E t + ζ²) + b t`.
2. `regularized_sqrt_hasDerivWithinAt` — the forward derivative alone:
   `HasDerivWithinAt (fun r => √(E r + ζ²)) (E' t / (2 √(E t + ζ²))) (Ici t) t`,
   from `HasDerivWithinAt E (E' t) (Ici t) t` and `E t ≥ 0`.
3. `regularized_sqrt_deriv` — the combined corollary (derivative ∧ bound), the
   manuscript's `appendix-a:139-143` step in one statement.
4. `primitive_integrand_intervalIntegrable` — `s ↦ K s · √(E s) + b s` is
   `IntervalIntegrable` on `[t₀, t]` for every `t ∈ Icc t₀ t₁`, from the
   `ContinuousOn` hypotheses. This is the integrability conjunct A04's
   `highContinuationIntegral` asserts alongside the bound.
5. `sqrt_le_primitive_linear` — integral form, **no** `E t₀ = 0`:
   `√(E t) ≤ √(E t₀) + ∫_{t₀}^{t} (K √E + b)`.

## Relation to `Paper1.sqrt_energy_le_primitive` — generalizes AND restricts

The source proof's skeleton transferred essentially verbatim: regularize with
`√(E + δ²)`, differentiate via `HasDerivAt.sqrt` / `HasDerivWithinAt.sqrt`, show
`AntitoneOn` of `√(E+δ²) − primitive` with
`antitoneOn_of_hasDerivWithinAt_nonpos`, then `le_of_forall_pos_le_add` to let
`δ ↓ 0`. Adding the linear term `K t · E t` changed only the algebra in the
derivative bound; dropping `E t₀ = 0` changed only the endpoint arithmetic
(`√(E t₀ + δ²) ≤ √(E t₀) + δ` instead of `√(δ²) = δ`).

But Z1 does **not subsume** the Paper 1 lemma — it generalizes in two directions
and *restricts* in two others (reviewer finding 4):

* **Generalizes:** adds the linear term `K t · E t`; drops the initial vanishing
  `E t₀ = 0` (so it also serves C01's unit U5, whose eq:RL2 starts at `‖a‖₂`).
* **Restricts:** requires `b` (and `K`) `ContinuousOn (Icc t₀ t₁)` — Paper1 asks
  nothing of `b` beyond nonnegativity on `Ioo`; and it hard-codes the primitive
  as the Lebesgue interval integral `∫ (K√E + b)` — Paper1 takes an abstract
  primitive `N` with `HasDerivAt N (b t) t`, strictly more general (a derivative
  need not be the integrand of its own primitive without integrability).

Confirmed by the reviewer: recovering `sqrt_energy_le_primitive` from
`sqrt_le_primitive_linear (K := 0)` needs `ContinuousOn b` and `0 ≤ b` on `Icc`
added, plus `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`. Both
lemmas stay.

## The one real subtlety: the sharper pointwise bound for the integral form

`regularized_sqrt_bound` (hence `regularized_sqrt_deriv`) states the bound the
manuscript displays, `(√(E+ζ²))' ≤ K √(E+ζ²) + b` (linear in the *regularized*
quantity — the Grönwall-ready form). But the ζ↓0 integral form must compare
against an integrand that does **not** depend on ζ, so the antitone step in
`sqrt_le_primitive_linear` uses the strictly sharper pointwise bound
`(√(E+δ²))' ≤ K √E + b`, valid because

* `E / √(E+δ²) ≤ √E`  (equivalently `E ≤ √(E+δ²)·√E`, since
  `√E·√E = E ≤ √(E+δ²)·√E`), giving `K · E/√(E+δ²) ≤ K √E`, and
* `√E / √(E+δ²) ≤ 1`, giving `b · √E/√(E+δ²) ≤ b`.

With the sharper bound the difference `√(E+δ²) − (√(E t₀) + ∫(K√E+b))` is
antitone, so `√(E t + δ²) ≤ √(E t₀) + ∫(K√E+b) + δ`, and `δ↓0` closes it. Had I
used only the manuscript's `≤ K√(E+ζ²)+b`, the integrand would carry
`√(E+ζ²)` and the `ζ↓0` limit would need dominated/monotone convergence inside
the integral — avoidable, and avoided.

Key algebra lemma used in Lean: `E x ≤ √(E x + δ²) · √(E x)` proved by
`nlinarith [hle, hsqE, Real.sqrt_nonneg (E x)]` where `hle : √E ≤ √(E+δ²)` and
`hsqE : √E · √E = E x` (`Real.mul_self_sqrt`). Then two
`mul_le_mul_of_nonneg_left` steps feed the final `nlinarith` after clearing the
denominator with `div_le_iff₀`.

## Hypotheses vs the paper — what is stronger

* The forward derivative is one-sided (`HasDerivWithinAt … (Ici t)`), weaker
  than `HasDerivAt`, matching the forward-in-time energy derivative; the
  fixed-`t` lemmas are applied by a consumer at each `t ∈ Ico t₀ t₁`.
* `sqrt_le_primitive_linear` requires `E, K, b` **`ContinuousOn (Icc t₀ t₁)`**.
  This is stronger than the paper's `L¹`-in-time Grönwall coefficient. The
  antitone proof needs the primitive's derivative to equal `K√E + b` at *every*
  interior point (`intervalIntegral.integral_hasDerivAt_right`, which wants
  `ContinuousAt` of the integrand); `IntervalIntegrable` alone gives an a.e.
  derivative, which `antitoneOn_of_hasDerivWithinAt_nonpos` cannot consume. These
  Sobolev norms are continuous in time along a classical solution (unit **N1**),
  so continuity is available where Z1 is consumed. This `ContinuousOn`
  strengthening is exactly lane 041's `gronwall_integral` shape, into which Z1's
  conclusion drops as `hstep` (`y = √E`, `c = K`).
* Nonnegativity of `K`, `b` is required only on `Ioo t₀ t₁` (interior times,
  matching the paper's differential inequality); `E ≥ 0` is required on the
  closed `Icc` because it is applied at `t₀` (the endpoint step `hsqrtt0`).

## Approaches considered and discarded

* **FTC-2 on `√(E+δ²)` directly** (`integral_eq_sub_of_hasDeriv_right_of_le`,
  then `intervalIntegral.integral_mono_on`): would need
  `IntervalIntegrable (fun x => E' x / (2√(E x+δ²)))`, which is not available —
  `E'` has no lower bound, so the regularized derivative need not be integrable.
  The antitone route needs only the sign of the derivative, never its integral.
* **Stating the exported bound with the sharper `≤ K√E + b`**: rejected for the
  displayed lemmas, because the task and manuscript (`appendix-a:139-143`) show
  the Grönwall-ready `√(E+ζ²)` form. The sharper bound is derived inline inside
  `sqrt_le_primitive_linear` where it is actually needed.
* **`positivity`**: it *does* close `0 < E t + ζ²` and `0 < E x + δ²` at these
  pins — its core scans the local context, so with `hEt : 0 ≤ E t` (resp.
  `hEx`) and `hζ`/`hδ` in scope it succeeds (reviewer finding 1; the template
  `Paper1/ScalarEnergy.lean:56` already uses `by positivity` for `0 < 2√(…)`).
  The current module uses `by positivity` for the `E + ζ²`/`E + δ²` goals and
  discharges the denominators `0 < 2√(…)` from the already-computed `hSpos` via
  `mul_pos`. (positivity fails only without any nonnegativity hypothesis on
  `E`, e.g. a bare `0 < E x + δ²` with no `hEx`.)
* **`set g`/`set N` to fold the goal integral**: avoided folding fragility by
  using `let g`/`let N`/`let G` and definitional unfolding (`show`,
  `simp only [g]`, `simp only [G]`), exactly as `sqrt_energy_le_primitive` does.

## Mathlib names used

`HasDerivWithinAt.sqrt`, `HasDerivAt.sqrt`, `HasDerivWithinAt.add_const`,
`HasDerivAt.add_const`, `HasDerivAt.const_add`, `HasDerivAt.sub`,
`HasDerivAt.hasDerivWithinAt`; `antitoneOn_of_hasDerivWithinAt_nonpos`,
`convex_Icc`, `interior_Icc`; `intervalIntegral.integral_hasDerivAt_right`,
`intervalIntegral.continuousOn_primitive_interval'`,
`intervalIntegral.integral_same`, `ContinuousOn.intervalIntegrable_of_Icc`,
`ContinuousOn.aestronglyMeasurable`, `StronglyMeasurableAtFilter` (anon ctor),
`Icc_mem_nhds`, `left_mem_uIcc`, `uIcc_of_le`, `measurableSet_Icc`,
`ContinuousOn.sqrt`, `ContinuousOn.continuousAt`, `ContinuousOn.mul`,
`ContinuousOn.add`, `ContinuousOn.mono`; `Real.sqrt_pos`, `Real.sq_sqrt`,
`Real.mul_self_sqrt`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Real.sqrt_nonneg`;
`div_le_iff₀`, `mul_le_mul_of_nonneg_left`, `mul_pos`,
`le_of_forall_pos_le_add`, `Ioo_subset_Icc_self`, `Icc_subset_Icc_right`.
`intervalIntegral.continuousOn_primitive_interval'` is only reachable with the
`intervalIntegral.` prefix under the file's `open Set MeasureTheory Topology`
(reviewer confirmed the bare name is `Unknown identifier`). Requires
`open Topology` for the `𝓝` neighborhood-filter notation.

## Review fixes (ACCEPT-WITH-NOTES, `REVIEW_Z1.md`)

Applied after the `ACCEPT-WITH-NOTES` verdict. No mathematical defect was
found; all findings were ergonomics/documentation.

* **Finding 3 (code).** Weakened `hKnonneg` and `hbnonneg` in
  `sqrt_le_primitive_linear` from `Icc t₀ t₁` to `Ioo t₀ t₁`, and changed the
  two use sites to `hKnonneg x hx` / `hbnonneg x hx` (they sit under
  `hx : x ∈ Ioo t₀ t₁`). `hEnonneg` stays on `Icc` (used at `t₀`).
* **Finding 5 (code).** Split `regularized_sqrt_deriv` into
  `regularized_sqrt_hasDerivWithinAt` (derivative only) and
  `regularized_sqrt_bound` (freestanding inequality on a scalar `d`, no
  derivative hypothesis). Kept `regularized_sqrt_deriv` as the combined
  corollary built from the two, so consumers holding either a one- or two-sided
  derivative can reuse the pieces they need.
* **Finding 6 (code).** Added `primitive_integrand_intervalIntegrable` exporting
  `IntervalIntegrable (fun s => K s · √(E s) + b s) volume t₀ t` on
  `t ∈ Icc t₀ t₁` — the conjunct `highContinuationIntegral` asserts.
  `sqrt_le_primitive_linear` now reuses it internally (for both `hgii` at `t₁`
  and `hii` at interior `x`).
* **Finding 1 (record).** Rewrote the `positivity` bullet: `positivity` does
  close the `0 < E + ζ²` / `0 < E + δ²` goals via its local-hypothesis fallback;
  the module now uses `by positivity` for those.
* **Finding 2 (docstring).** Fixed the paper citations after opening the files:
  ζ device for the `L²` packet at `02-preliminaries.tex:140-143` (the ζ sentence
  is `:143`), subcritical bound at `04-whole-space.tex:100-102`, and eq:RL2 at
  `04-whole-space.tex:118-120`. The appendix range `:139-146` was correct.
* **Finding 4 (docstring + record).** Softened "generalizes
  `sqrt_energy_le_primitive`" to state both what is generalized (linear term, no
  `E t₀ = 0`) and what is restricted (`ContinuousOn b`, Lebesgue primitive), so
  the Paper 1 lemma is not claimed as a corollary; both stay.

Post-fix results: `lake build NSFormalization.Section4.A04.Regularized` →
`Built … (1.7s)`, 0 warnings; `lake env lean ../research/A04/axioms_z1.lean` →
all five declarations `[propext, Classical.choice, Quot.sound]`;
`make check` → exit 0 ("30 work items … consistent").
