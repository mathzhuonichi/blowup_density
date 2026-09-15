# A04 unit G2 — eq:highcontinuation before the limit (`regularizedNormDerivative`)

Lane 135. Module `formalization/NSFormalization/Section4/A04/HighContinuation.lean`.
Spec field `research/A04/Spec.lean:459-470`, unit **G2** of `COMPARISON.md` §4.

## What was proved (theorem names / exact statements)

* `Cgron (m : ℕ) (ν : ℝ) : ℝ := Chigh m ^ 2 / (4 * ν)` — the constant the Young
  absorption produces. **Exact constant `Cgron m ν = (Chigh m)² / (4ν)`**, where
  `Chigh m = A03.outerTameConst m = 6·vectorTameConst m` (from
  `EnergyIdentityHigh.lean`). The manuscript displays no formula
  (`Spec.lean:349-353`), so this is the derivation's value.
* `Cgron_pos : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < Cgron m ν` — `div_pos (pow_pos (Chigh_pos m) 2) …`.
* `young_high_real {d g a n F ν C : ℝ} (hν : 0 < ν)`
  `(h : (1/2)*d + ν*g^2 ≤ C*a*n*g + F*n) : (1/2)*d ≤ C^2/(4*ν)*a^2*n^2 + F*n`
  — the pure real-arithmetic Young step. Certificate: the perfect square
  `(2νg − Can)²/(4ν) ≥ 0`, produced by the `expand` identity + `field_simp; ring`,
  then `linarith`. No `nlinarith` needed.
* `young_absorption_high {m : ℕ} {ν d g a n F : ℝ} (hν : 0 < ν)`
  `(h : (1/2)*d + ν*g^2 ≤ Chigh m*a*n*g + F*n) : (1/2)*d ≤ Cgron m ν*a^2*n^2 + F*n`
  — the instance with the manuscript constants (`Cgron m ν = Chigh m ^2/(4ν)` by
  `rfl`, folded in via `linarith`).
* `deriv_normSq_absorbed` (**review finding (a) hoist**) — for `energyIdentityHigh`'s
  hypotheses and `t ∈ Ioo 0 T`:
  `∃ d, HasDerivAt (fun r => sobolevNormAt m w.velocity r ^ 2) d t ∧
   (1/2)*d ≤ Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 * sobolevNormAt m w.velocity t ^ 2
             + sobolevNormAt m f t * sobolevNormAt m w.velocity t`.
  Proof: `energyIdentityHigh` then `young_absorption_high`. This is the absorbed
  squared-norm derivative bound that was inline in `regularizedNormDerivative`;
  now named so unit **G2b** (`highContinuationIntegral`, `Spec.lean:471-494`) can
  feed it to `sqrt_le_primitive_linear`.
* `deriv_normSq_absorbed_deriv` — the `deriv`-valued form of the above via
  `HasDerivAt.deriv`:
  `(1/2) * deriv (fun r => sobolevNormAt m w.velocity r ^ 2) t ≤ Cgron m ν * … + …`.
* `regularizedNormDerivative` — the spec field token-for-token (see the
  conformance `example` in `axioms_high_continuation.lean`, which elaborates); now
  consumes `deriv_normSq_absorbed` instead of inlining the absorption.

All six `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

## Route

`energyIdentityHigh` (unit G1) → `⟨d₀, HasDerivAt (r ↦ ‖u(r)‖²_{H^m}) d₀ t, eq:Rhigh bound⟩`.

1. `HasDerivAt.sqrt` on `(hd.add_const (ζ^2))` with `hpos.ne'` gives the two-sided
   derivative of `r ↦ √(‖u(r)‖²_{H^m}+ζ²)`, value `d₀ / (2√(‖u‖²_{H^m}+ζ²))`.
2. `young_absorption_high hν hbound` absorbs the cross term →
   `½ d₀ ≤ Cgron·‖u‖²_{H²}·‖u‖²_{H^m} + ‖f‖_{H^m}·‖u‖_{H^m}`.
3. `rw [Real.sqrt_sq hnnn]` (with `hnnn : 0 ≤ sobolevNormAt m w.velocity t`,
   which is `ENNReal.toReal_nonneg` since `sobolevNormAt` is a `.toReal`) turns
   `‖u‖_{H^m}` into `√(‖u‖²_{H^m})`, then `linarith` gives the
   `d₀ ≤ 2(K·E + b·√E)` shape.
4. `regularized_sqrt_bound` (unit Z1, `Regularized.lean:65`) with
   `E := fun r => sobolevNormAt m w.velocity r ^ 2`,
   `K := fun _ => Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2`,
   `b := fun _ => sobolevNormAt m f t`, `d := d₀` divides by `2√(E+ζ²)` and
   produces exactly the spec RHS (beta-reduction + left-assoc of
   `Cgron m ν * a² * √(…)` is defeq to `K t * √(…)`, so `exact` closes).

## Load-bearing hypotheses

* `0 < ν` (`hν`) — **load-bearing.** Used by `Cgron_pos` and the Young division
  by `4ν`; and passed to `energyIdentityHigh`.
* `0 < ζ` (`hζ`) — **load-bearing.** Gives `hpos : 0 < ‖u‖²_{H^m}+ζ²` (so the
  square root is differentiable and `regularized_sqrt_bound` applies). At `ζ = 0`
  the derivative fails at a zero of `u` in `H^m` — this is exactly why the field
  is stated per fixed `ζ`.
* `HasSmoothSobolevPath T w.velocity` (`hpath`) — **load-bearing** (the
  differentiability input of `energyIdentityHigh`).
* `MemForceR f` (`hf`) — **load-bearing** (`energyIdentityHigh`'s forcing datum).
* `3 ≤ m` (`hm`), `t ∈ Ioo 0 T` (`ht`) — **load-bearing** (interior-time,
  order-≥3 hypotheses of `energyIdentityHigh`).
* `a ∈ initialClassR` (`ha`) — **NOT load-bearing** here; carried through to
  `energyIdentityHigh`, which itself does not use it (recorded in
  `ATTEMPTS_ENERGY_HIGH.md`). Kept for spec fidelity.

## Paths tried and errors

* **Two-sided vs one-sided derivative.** The brief suggested routing the
  derivative through `regularized_sqrt_hasDerivWithinAt` / `regularized_sqrt_deriv`.
  Those produce `HasDerivWithinAt _ (Ici t) t`, whereas the spec field states a
  **two-sided** `HasDerivAt` and `energyIdentityHigh` already delivers a two-sided
  `HasDerivAt (‖u‖²_{H^m}) d₀ t`. **Correction (review finding 2):** the blanket
  claim "a `HasDerivWithinAt` cannot be upgraded to `HasDerivAt`" is too strong —
  an `Ici` + `Iic` pair upgrades in two lines (`hl.union hr` then
  `Iic_union_Ici`, `hasDerivWithinAt_univ`). What is true is that the **single
  `Ici` half alone, which is all `Regularized.lean` exports**, cannot be upgraded;
  routing through it would mean inventing an `Iic` twin for no gain when
  `energyIdentityHigh` already hands over a two-sided `HasDerivAt`. So the correct
  route is the two-sided `HasDerivAt.sqrt` directly. Only the **inequality** half
  of unit Z1, `regularized_sqrt_bound` (which takes a bare scalar `d`, no
  derivative hypothesis — this is exactly why Z1's review finding 5 split it out),
  is consumed. No mathematical content is lost.
* `HasDerivAt.add_const` — **the symptom is real but the earlier diagnosis was
  wrong (review finding 1).** `#check @HasDerivAt.add_const` does report
  `Unknown constant` (even under the full module imports), but this is **not** a
  missing-import problem: there is no constant of that exact name. The term-level
  `h.add_const (ζ^2)` compiles fine even under a minimal
  `import Mathlib.Analysis.SpecialFunctions.Sqrt`, because generalized dot notation
  unfolds `HasDerivAt` and resolves it to **`HasFDerivAtFilter.add_const`**
  (confirmed by `#print` with `pp.fullNames`). No import change is or was needed.
  Lesson corollary: here even `#check` on the guessed dotted name misleads, because
  dot notation resolves through the unfolding — the working term settles existence.
* `young_high_real`'s `expand` identity: `field_simp; ring` (with `ν ≠ 0` in
  context). `nlinarith` on the divided form was not attempted because the
  perfect-square certificate is cleaner and division-free after `field_simp`.
* No `set_option maxHeartbeats` was needed; the module builds in ~2.8 s under the
  default budget.

## What the next A04 contract version should register

**Correction to the earlier premise (coordinator note):** A04's V1 contract
**`A04.energy_high_partial`** was merged as **PR #134** while this lane ran (the
review, written against an older tree, said "no A04 contract at any version" —
superseded). So the next registration is a **V2**, not a fresh V1. V2 should add
**`Cgron`** (→ `A04.Cgron`), **`Cgron_pos`** (→ `A04.Cgron_pos`),
**`regularizedNormDerivative`** (→ `A04.regularizedNormDerivative`), and
**`highContinuationIntegral`** — and should be opened **after G2b lands**, so the
only in-tree consumer of `regularizedNormDerivative` (which is G2b) exists before
its spelling is frozen by CI. Carry `Cgron` as the spec's **opaque** `ℕ → ℝ → ℝ`
field plus `Cgron_pos`; the value `(Chigh m)²/(4ν)` belongs only in the **binding**
(`Spec.lean:349-353`: "the manuscript displays no formula, so none is pinned"). No
`rfl` bridge is owed for `Cgron` — it is a fresh `def` with no upstream original;
the conformance `example` in `axioms_high_continuation.lean` is the fidelity check.

## MAINT notes (from review findings 3-4; do not act on them in this lane)

* **Dead-code Z1 lemmas.** `regularized_sqrt_hasDerivWithinAt` and
  `regularized_sqrt_deriv` (`Regularized.lean`) have **zero consumers tree-wide**
  (grep: only docstrings + `axioms_z1.lean`); even `sqrt_le_primitive_linear`
  inlines its own `.sqrt`. **Keep them** — they are the literal Z1 deliverable of
  the `COMPARISON.md` booking and the `02-preliminaries.tex:152` /
  `04-whole-space.tex:103,121` ζ-reuse sites (C01/I01) have not been built yet.
  Revisit once those land; if they also go two-sided, drop both.
* **`Cgron` shadowing.** `def Cgron` now lives in `NSFormalization.Section4.A04`,
  where two existing declarations bind a *local* `Cgron` of a different type:
  `Gronwall.lean:202` (`gronwall_integral_mul {… Cgron : ℝ …}`) and
  `Continuity.lean:132` (`intervalIntegrable_highContinuationIntegrand … (Cgron : ℕ → ℝ → ℝ)`).
  Everything compiles (locals shadow; `make test` green), but the **G2b lane must
  pass `A04.Cgron` explicitly** when applying `intervalIntegrable_highContinuationIntegrand`,
  or it gets the binder, not the def. A MAINT rename of the binders (`Cg`, `Ccoef`)
  would remove the trap; not touched here.

## Commands

* `lake build NSFormalization.Section4.A04.HighContinuation` → `Built … (2.8s)`,
  no warnings from the module (only pre-existing vendor HeliCorgi warnings).
* `lake env lean ../formalization/NSFormalization/Section4/A04/HighContinuation.lean`
  → silent, exit 0.
* `lake env lean ../research/A04/axioms_high_continuation.lean` → all four
  declarations `[propext, Classical.choice, Quot.sound]`, conformance `example`
  elaborates, exit 0.
* `make check` → exit 0 ("30 work items … consistent"; contract-policy tests OK).
