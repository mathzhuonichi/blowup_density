# ATTEMPTS — lane 132 (D01 · C1b-m-D close: rows D-b-transport + D-close)

Deliverable: `formalization/NSFormalization/Section4/D01/FiniteOrderConstructor.lean`
(namespace `NSFormalization.Section4.D01`).  All eight new declarations build and print exactly
`[propext, Classical.choice, Quot.sound]` (`research/D01/axioms_finite_order_close.lean`).

## What was proved

* `isSobolevDatum_partialDeriv_weak`, `db_cycles_full` — promoted verbatim from the lane-125
  reviewer probes (`rev125_partialderiv_weak.lean`, `rev125_db_cycles.lean`) into a registered
  module (credit noted in docstrings).
* `memLp_coord_smul_datum` — row D-b-transport (the new work).
* `HasWeakDerivsL2`, `weakDerivs_mono`, `exists_isSobolevDatum_of_memLp_derivs` — row D-close.
* `smoothField_weakDeriv_pairing`, `weakDerivs_smooth` + two `example`s — non-vacuity/consistency.

## The transport (row D-b-transport): the key positive finding

The reviewer's §5 recipe pointed at the `Transverse.lean:177-205` template (cycles→angular transport
of the *same expression* `ξⱼ·(A i)`), which juggles the symbol `2πi·(1+‖ξ‖²)^{-1/2}` and the weight
`angularWeightSymbol` and cancels them factor by factor.  **That machinery is not needed here.**  The
decisive observation: `db_cycles_full` is stated about `(cyclesToAngular s).symm (A i)` and
`(cyclesToAngular s).symm (C j i)`, and `cyclesToAngular s = angularFrequencyDilation ∘
angularWeightEquiv s` (`AngularTameProduct.lean:11`, `rfl`).  So

    (A i)(ξ)   =ᵐ frequencyUnit^{-3/2} · angularWeightSymbol s (c⁻¹ξ) · f(c⁻¹ξ)
    (C j i)(ξ) =ᵐ frequencyUnit^{-3/2} · angularWeightSymbol s (c⁻¹ξ) · g(c⁻¹ξ)

with `f = (cyclesToAngular s).symm (A i)`, `g = (cyclesToAngular s).symm (C j i)`, `c = frequencyUnit`.
The dilation factor `frequencyUnit^{-3/2}` and the Bessel weight `angularWeightSymbol s (c⁻¹ξ)` are
**identical on both sides**.  Substituting `db_cycles_full` transported to `c⁻¹ξ`
(`g(c⁻¹ξ) = 2πi·(c⁻¹ξ)ⱼ·f(c⁻¹ξ)`, and `(c⁻¹ξ)ⱼ = c⁻¹·ξⱼ` by `rfl`) makes both factors cancel,
leaving the division-free identity

    (2πi) · (ξⱼ)·(A i)(ξ)  =ᵐ  (frequencyUnit) · (C j i)(ξ).

Since `C j i ∈ L²`, the RHS is `MemLp`; `memLp_congr_ae` + one `MemLp.const_smul (2πi)⁻¹` gives
`MemLp (ξ ↦ (ξⱼ)·(A i)(ξ))`, the shape `raisableWitness_of_memLp_smul` consumes.

### Mechanics that worked / had to be nailed
* `cyclesToAngular s f = angularFrequencyDilation (angularWeightEquiv s f)` is `rfl`
  (`.trans` coe); and `((c⁻¹•ξ) j : ℝ) = c⁻¹ * ξ j` is `rfl` (EuclideanSpace smul).  Both verified in
  a throwaway probe before writing the module.
* Transport of an `∀ᵐ` fact by `ξ ↦ c⁻¹•ξ`: exactly the `Transverse.lean:186-191` pattern
  `hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure hP κm)` with
  `hMP := ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume (inv_ne_zero …)⟩`.
* The final a.e. equation is closed by `linear_combination`, treating `↑c, ↑c⁻¹`, the weight and
  `f(c⁻¹ξ)` as atoms.  The one scalar fact fed in is `hcc : (↑c⁻¹)*(↑c) = 1`
  (`← Complex.ofReal_mul, inv_mul_cancel₀ hc0.ne', Complex.ofReal_one`); no `field_simp` on opaque
  atoms is needed.  Chosen the **division-free** form `(2πi)·LHS = c·RHS` precisely so that `↑c·↑c⁻¹`
  combines via `hcc` rather than requiring `ring` to know `↑c⁻¹ = (↑c)⁻¹`.

### Negative attempts / dead ends
* First `linear_combination` had **both coefficient signs flipped**: the residual `ring` goal came out
  as `… * 4 - … * 2 = 0` (i.e. the `2πi`-doubling instead of cancellation), exact error text
  `ring failed, ring expressions not equal`.  Fix: `coeff₁ = +(↑c·↑w3·Ω)` on the db identity,
  `coeff₂ = −(2πi·↑ξⱼ·↑w3·Ω·f)` on `hcc`.  Recorded because the sign is easy to get wrong and the
  error is opaque.
* `MemLp.const_smul` produces `MemLp (c • ⇑Cji)` (function-level smul), which does **not** directly
  unify with the goal `MemLp (fun ξ => ↑c • (Cji) ξ)` — error `Type mismatch … (c • ↑↑↑Cji) vs
  (fun ξ => …)`, and `simpa` made it worse by rewriting `•`→`*` only in the goal.  Fix: route through
  `(memLp_congr_ae ?_).mp` with `filter_upwards with ξ; rw [Pi.smul_apply, smul_eq_mul]`.
* Considered defining the constant as `κ := ↑c/(2πi)` and proving `(ξⱼ)·(A i) =ᵐ κ·(C j i)` directly,
  but the pointwise identity then needs `(2πi)/(2πi)=1` and `↑c/(↑c)=1` which `ring` cannot do without
  `field_simp` on opaque atoms.  The division-free `(2πi)·LHS = c·RHS` route avoids this entirely.

## The constructor (row D-close): the hypothesis-shape decision

Chose to expose the Euler-facing hypothesis as a **recursive predicate** `HasWeakDerivsL2 z m`:
`m=0` ⇒ `MemLp z 2`; `m=k+1` ⇒ `MemLp z 2` and, per coordinate `j`, an `L²` field `w` (the weak
`∂ⱼz`) with `HasWeakDerivsL2 w k` **and** the Schwartz pairing `∫ψ·wᵢ = ∫(−∂ⱼψ)·zᵢ`.  Rationale:
this is the iterated form of the *exact* hypothesis shape `db_cycles_full`/`isSobolevDatum_partialDeriv_weak`
already consume (reuse without adapters), and it is what C1b-m-E's `word_hasDerivAt` delivers via
integration by parts (row D-euler-pairing).  Considered stating the hypothesis with iterated
`iteratedFDeriv`/multi-index words directly, but that would require an adapter to the Schwartz-pairing
shape at every induction step; the recursive predicate keeps the derivative of `∂ⱼz` bookkeeping
trivial (the `w` of the step is literally the `z` of the recursive call).

### Bookkeeping that had to be right
* `weakDerivs_mono m z : HasWeakDerivsL2 z (m+1) → HasWeakDerivsL2 z m` — needed because the
  induction step applies the IH to `z` itself at one lower order; proved by its own recursion on `m`
  (the `∂ⱼz` of `z(m+2)` carries order `m+1`, dropped to `m` by the recursive `weakDerivs_mono m`).
* Order cast at the successor: goal order `((m+1:ℕ):ℝ)`; rewrote with
  `show (((m+1:ℕ)):ℝ) = (m:ℝ)+1 from by push_cast; ring` so `isSobolevDatum_raise` (output order
  `(m:ℝ)+1`) applies.  Base case: `rw [show ((0:ℕ):ℝ) = (0:ℝ) from Nat.cast_zero]` (LESSONS 09-14
  line 3: `simp only [Nat.cast_zero]` reports "no progress" because the type depends on the cast).
* `choose w hwwd hwpair using hstep` and `choose C hCd using hCex` to turn the per-`j` existentials
  into the families `memLp_coord_smul_datum` expects.

## Non-vacuity (`weakDerivs_smooth`) and the pairing

`smoothField_weakDeriv_pairing` = the reversal of the realization chain of
`DerivativeDatum.isSobolevDatum_partialDeriv` (lines 27-38) with no datum: from
`physicalDistribution_directionalField` (`Source/PhysicalSobolevDistribution.lean:29`) and
`TemperedDistribution.lineDerivOp_apply_apply`, integration by parts for a smooth `L²` field is a
~10-line lemma.  `weakDerivs_smooth` recurses with `w = (Z.directionalField (coordinateVector j)).field`
(a `SmoothL2Field` again, so the recursive `HasWeakDerivsL2 w m` is `weakDerivs_smooth m (Z.directionalField …)`).

### Negative: un-beta-reduced goal
First wrote the pairing's two integral congruences with
`integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))`; the goal came back as the beta-redex
`(fun x => …) x = (fun x => …) x` and `rw [componentField_field]` failed with
`Tactic rewrite failed: Did not find an occurrence of the pattern`.  Fix: `refine integral_congr_ae ?_;
filter_upwards with x; rw […]` (filter_upwards beta-reduces).

## Commands run (all from `verification/`, `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`)

* `lake build NSFormalization.Section4.D01.FiniteOrderConstructor` — success (9926 jobs).
* `lake env lean ../formalization/NSFormalization/Section4/D01/FiniteOrderConstructor.lean` — silent (exit 0).
* `lake env lean ../research/D01/axioms_finite_order_close.lean` — all 8 print `[propext, Classical.choice, Quot.sound]`.
* `make check` — pass (contract policy 13 tests OK; work queue consistent).

## Review follow-up (REVIEW_FINITE_ORDER_CLOSE.md, applied by the lead as records only)

- Dead end 2 was misdiagnosed: `MemLp.const_smul` does apply directly (`*`, `•` and the un-eta'd form all `exact`); only the `simpa` route fails, with the recorded error text. Consequence: the three-line `memLp_congr_ae` detour in `memLp_coord_smul_datum` is removable — **left for the next D01 SIMP pass** (statements unchanged either way). Lesson recorded in `logs/LESSONS.md`: `simpa using h` normalises `•` to `*` in the hypothesis and manufactures a spurious unification failure; try bare `exact` first.
- Module docstring wording: the surviving `frequencyUnit` factor comes from the coordinate rescaling, not from the dilation Jacobian (the Jacobian `c^{-3/2}` cancels) — the ATTEMPTS text is the correct one; docstring fix deferred to the SIMP pass.
- The angular-variable identity is only an internal `have`; row D-euler-coord will want it exported (next D01/Euler lane).
- `research/D01/probes/rev125_{partialderiv_weak,db_cycles}.lean` are now byte-identical to tree lemmas — MAINT cleanup.
- Reviewer's Euler-side answer (for the next lane, D-euler-pairing): `sobolevTranslation` is coordinatewise (`rfl`-level), so invariance transfers to every derivative word by `congrArg`; E1 (≈60–90 lines, bookkeeping: `word_has_jet` → `ofJet` → `exists_ordinary_value`, matching `(ofJet J).val w'` with `word 1 u _ (w'++w)`) and E2 (≈60–120 lines: `HasDerivAt (fun t => translation (t • eⱼ) z) w 0 → ∫ψ·wᵢ = ∫(−∂ⱼψ)·zᵢ`, via translation invariance of the measure moved onto `ψ`, no cutoff needed; cheaper route through `⟪ψ, translation(teⱼ)z⟫ = ⟪translation(−teⱼ)ψ, z⟫` + `SmoothL2Field.translation_contDiff`, ≈40 lines). Caveat: `exists_local`'s `T` depends on `q` and E1 spends three orders, so the chain yields each finite order `m ≤ q−2` on its own `T(q)`, not one `T` for all orders (regularity persistence is a separate obligation). Consumer: add `exists_isSobolevDatum_m_ordinaryL2` to `CarrierBridge.lean` once D-euler-pairing lands; `DatumPathContinuity.lean` should not consume it (raising is not a CLM).
