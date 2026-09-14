# A3-M2 — `gronwall_bddAbove_Ico` instantiation on a classical solution (lane 142)

Module: `formalization/NSFormalization/Section4/A01/GronwallInstance.lean`
Axioms/non-vacuity: `research/A01/axioms_a3_m2.lean`

## What was proved

Two theorems in namespace `NSFormalization.Section4.A01`:

* `highOrder_bddAbove_of_kbnd` — one order. For `w : ClassicalSolutionR ν a f T` with
  `0<ν`, `a∈initialClassR`, `MemForceR f`, `MemL1Hm f`, `HasSmoothSobolevPath T w.velocity`,
  `m≥3`, `0<T₀≤T`, and the single explicit hypothesis
  `hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in 0..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd`,
  concludes
  `∀ t ∈ Ico 0 T₀, sobolevNormAt m w.velocity t ≤ (sobolevNormAt m w.velocity 0 +
     (forceSobolevENormL1 m f).toReal) * Real.exp (A04.Cgron m ν * Kbnd)`.
* `highOrder_bddAbove_all_orders_of_kbnd` — same hypotheses minus the fixed `m`, concludes
  `∀ m : ℕ, 3 ≤ m → BddAbove ((fun t => sobolevNormAt m w.velocity t) '' Ico 0 T₀)` via
  `higherOrder_bddAbove_fixedDriverSq` (driver `m_drive := 2`, one `Kbnd`, one `T₀`).

`#print axioms` on both, and on the two zero-solution non-vacuity instances, is exactly
`[propext, Classical.choice, Quot.sound]`.

## The slot-by-slot instantiation (per A3_SPLIT §3.5, review §5)

All slots discharged as the table said:
`hCgron ← (A04.Cgron_pos m ν hν).le`; `hy0 ← A01.sobolevNormAt_nonneg`;
`hy ← (A04.continuousOn_sobolevNormAt_velocity w m).mono`; `hk ← that at order 2, `.pow 2`;
`hknn ← sq_nonneg`; `hb`/`hbnn`/`hbbnd ← A01.forceCap_L1` (chosen route, see decision);
`hstep ← A04.highContinuationIntegral … 0 t … |>.2`.

**`hstep` needed NO adapter.** `highContinuationIntegral`'s conclusion at `t₀ := 0` is,
token for token, `gronwall_bddAbove_Ico`'s `hstep` with `y := fun t => sobolevNormAt m
w.velocity t`, `k := fun s => sobolevNormAt 2 w.velocity s ^ 2`, `b := fun s => sobolevNormAt
m f s`, `Cgron := A04.Cgron m ν`. The two integrands agree up to β and left-association of
`*` (`Cgron * k s * y s = (Cgron * (sobolevNormAt 2 …)^2) * sobolevNormAt m …`, exactly
`highContinuationIntegral`'s `Cgron m ν * sobolevNormAt 2 … ^ 2 * sobolevNormAt m …`), so a
bare `.2` term is accepted by `exact`/argument-passing — no `intervalIntegral.integral_congr`,
no `ring_nf`. This confirms the review's "same parse, no adapter" prediction.

## Decisions

* **`Bbnd` route.** Used `forceCap_L1` (needs only `MemForceR f`, no `hT₀`), giving the
  *explicit* constant `Bbnd := (forceSobolevENormL1 m f).toReal` and a fully-explicit bound,
  rather than `forceCap`'s existential `∃ Bbnd`. This matches "explicit bound" in the brief
  and keeps `A04.Cgron m ν`, `Kbnd`, `Bbnd` all named in the conclusion.
* **`hT₀ : 0 < T₀` is unused** on the L¹ route (positivity of the horizon is needed for
  neither `forceCap_L1` nor `highContinuationIntegral`'s `t < T`, which only needs `T₀ ≤ T`).
  Kept in the signature for interface fidelity to the A3 story (a genuine horizon), binder
  renamed `_hT₀` to silence the `unusedVariables` linter (else `lake env lean` is not silent).

## Failed approaches / errors seen and fixed

1. **`∀ m` in part 2 elaborated as `ℝ`, not `ℕ`.** Writing the conclusion as
   `∀ m, 3 ≤ m → BddAbove ((fun t => sobolevNormAt (m : ℝ) …) …)` made Lean infer `m : ℝ`
   (`(m : ℝ)` becomes the identity coercion). Exact error:
   `higherOrder_bddAbove_fixedDriverSq … has type ∀ (m : ℕ), 3 ≤ m → BddAbove ((fun t =>
   sobolevNormAt (↑m) w.velocity t) '' Ico 0 T₀) but is expected to have type ∀ (m : ℝ), 3 ≤ m
   → BddAbove ((fun t => sobolevNormAt m w.velocity t) '' Ico 0 T₀)`. Fix: state `∀ m : ℕ`.
2. **`hT₀` unused warning** (see decision above): `Variable name hT₀ is not explicitly
   referenced` → renamed `_hT₀`.
3. **Axioms file `(0 : SpatialField)`** raised `failed to synthesize OfNat SpatialField 0` /
   `Membership SpatialField (Set …SpatialField)`. Fix: write `(0 : Space → Space)` (the
   `abbrev`-unfolded type, which has `Pi.instZero`), defeq to `A02.SpatialField`.
4. **Axioms file `A04.Cgron` `Unknown identifier`** — in namespace `Lane142` the prefix `A04.`
   does not resolve via parent-namespace search. Fix: `open …A04 (Cgron …)` and write `Cgron`.
5. **Axioms file `forceSobolevENormL1` `Ambiguous term`** (`D01` and `A04` both export it).
   Fix: open only `A04`'s (the one the module's conclusion uses), selectively.

## Note on `(2 : ℝ)` vs `((2 : ℕ) : ℝ)`

`k`/`hkbnd` use `sobolevNormAt 2 …` (literal `2 : ℝ`); the continuity slot uses
`continuousOn_sobolevNormAt_velocity w 2` (arg `2 : ℕ`, so `sobolevNormAt ((2:ℕ):ℝ) …`); and
`higherOrder_bddAbove_fixedDriverSq (m_drive := 2)` produces `(y 2 s)` with the ℕ-cast. These
unify by `isDefEq` in this Mathlib pin — the same reliance `A04.HighContinuationIntegral`'s
`hKc` already has, so it is not a new assumption.

## The residual hole — row A3-L1·k (consumer's exact expected shape)

The single remaining input `hkbnd` that A3-L1·k must deliver, in these exact terms, is

```
hkbnd : ∀ t ∈ Ico (0:ℝ) T₀, (∫ s in (0:ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd
```

i.e. a single real `Kbnd` capping the running `L²_t H²` energy of the velocity on `[0,T₀)`
(`sobolevNormAt 2 w.velocity s = ‖u(s)‖_{H²}`, so the integrand is `‖u(s)‖²_{H²}`; note the
literal `2 : ℝ` order, matching `A04.highContinuationIntegral`).

How `exists_local`'s clause supplies it once the order-2 cap exists: `exists_local`
(`Source/OrdinaryForcedLocal.lean:32`) delivers `‖u‖ ≤ ‖u₀‖+1` in the fixed order-`q+1`
cylinder sup-norm on `[0,T]`. The still-open `D-euler-pairing` step (the Euler-side
`HasWeakDerivsL2 (⇑(U t)) 2`, `MemLp 2` + order-≤2 Schwartz-pairing IBP) is what turns this
sup-norm into a `t`-free order-2 datum comparison `sobolevNormAt 2 (⇑(U t)) ≤ c·‖u t‖_{H^{q+1}}`
with `c` independent of `t`. Given that, the pointwise bound `sobolevNormAt 2 w.velocity s ≤
c·(‖u₀‖+1)` holds for `s ∈ [0,T₀)`, so
`∫ s in 0..t, ‖u‖²_{H²} ≤ ∫ s in 0..t, c²·(‖u₀‖+1)² ≤ c²·(‖u₀‖+1)²·T₀ =: Kbnd`
(a finite `t`-free constant), which is exactly the shape above. Until `D-euler-pairing` lands
the order-2 `sobolevENorm` can be `⊤` (vacuously `sobolevNormAt = 0`), so `Kbnd := 0` is only
demonstrably correct on the zero solution (the non-vacuity witness here).

## Commands run

* `cd verification && lake build NSFormalization.Section4.A01.ForceCap
  NSFormalization.Section4.A04.HighContinuationIntegral` — success (deps).
* `cd verification && lake build NSFormalization.Section4.A01.GronwallInstance` —
  `Built … (2.7s)`, `Build completed successfully`.
* `cd verification && lake env lean ../formalization/NSFormalization/Section4/A01/GronwallInstance.lean`
  — EXIT 0, silent.
* `cd verification && lake env lean ../research/A01/axioms_a3_m2.lean` — EXIT 0, all four
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
* `make check` — passes (contract policy 13 tests OK; work queue consistent).

## Review follow-up (REVIEW_A3_M2.md, applied by the lead as records only)

- Fidelity (reviewer): with `T₀ := T` the theorem is literally `appendix-a-local-theory.tex:146-147` ("If eq:criterion holds, Grönwall bounds every H^m norm uniformly up to S"); `Kbnd` is the `L²_tH²` quantity of eq:criterion (`02-preliminaries.tex:111`) and the exponent constant is eq:highcontinuation's `C_{m,ν}`. The `⊤` trap does not occur on the R³ side (`w.sobolev 2` gives a true datum); the vacuity warning in `A3_SPLIT.md` concerns only the cylinder side `⇑(U t)`.
- `hf1 : MemL1Hm f` is not load-bearing (derivable via `memL1Hm_of_memForceR`; `highContinuationIntegral` binds it as `_hf1`); kept for interface fidelity.
- **The `hkbnd` hole is a value, not a possibility, and narrower than recorded**: for any classical solution and any `T₀ < T` some `Kbnd` exists for free (order-2 norm continuous on `Ico 0 T` ⇒ bounded on `Icc 0 T₀` ⇒ `Kbnd := max M 0 · T₀`), with no Euler-side input; the reviewer proved this (`probes/rev142_*` if preserved) and also that `hkbnd` is load-bearing (`Kbnd` free collapses the bound). What A3-L1·k genuinely owes is the **endpoint case `T₀ = T`** (a `Kbnd` finite as `T₀ ↑ T`, i.e. eq:criterion itself).
- Recorded failure 4 (`(0 : SpatialField)` `OfNat`): the true cause is `autoImplicit` binding the un-`open`ed name `SpatialField` as a free variable (the error's second line shows `Membership SpatialField (Set …A02.SpatialField)` with two different types); adding `SpatialField` to the `open` list fixes it. Lesson recorded in `logs/LESSONS.md`.
- The zero solution has now been rebuilt eight times across reviews and lanes — MAINT: land it once.
- `HasAprioriBound` (lane 139) is not yet reachable from `highOrder_bddAbove_of_kbnd`: still owed are the converse norm comparison (cylinder ≤ R³ side, `REVIEW_A2B_INV.md:242-247`), the `Ico 0 T₀ → Icc 0 T` widening, and the mild ⇒ energy bridge inside `hbound` — rows to add to `A3_SPLIT.md`. Suggested order: D-euler-pairing (140) → those three rows → A3-L1·k → A3-Tm → T1 → B1 (L, the largest block) → B2 → X1.
