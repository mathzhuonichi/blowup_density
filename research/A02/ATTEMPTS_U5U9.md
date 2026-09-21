# A02 units U5 (`patch`) and U9 (`lifespan_le_of_unbounded`) — attempts and route notes

Lane 058, task A02. New module
`formalization/NSFormalization/Section4/A02/Patch.lean`; conformance file
`research/A02/axioms_u5u9.lean`. Both units proved, `sorry`-free, transitive
axioms exactly `propext, Classical.choice, Quot.sound`.

## What was proved

* `NSFormalization.Section4.A02.patch` — spec field `MaximalSolutionAPI.patch`
  (`Spec.lean:357-367`), verbatim type.
* `NSFormalization.Section4.A02.lifespan_le_of_unbounded` — spec field
  `MaximalSolutionAPI.lifespan_le_of_unbounded` (`Spec.lean:576-582`), verbatim
  type, with the local `limsupLeft`/`speedENorm`.

Supporting declarations in the same module: `limsupLeft`, `speedENorm` (restated
verbatim from `Spec.lean:135-136,148-149`), `PressureGaugeEquivOn.{refl,symm,mono}`,
`speedENorm_le_ofReal`.

## Route taken

### U5 `patch` — WLOG the longer horizon, no gluing
Exactly the COMPARISON row-U5 recommendation. `rcases le_total T₁ T₂`, then
`rw [max_eq_right h]` / `rw [max_eq_left h]` reduces `max T₁ T₂` in the
existential's *binder type* to the larger horizon, so the witness `w` is
**literally** `u₂` (resp. `u₁`) — no cast, no transport structure needed. The
four agreement clauses are then:
* agreement with the longer solution: `fun _ _ _ => rfl` (velocity) and
  `PressureGaugeEquivOn.refl` (pressure);
* agreement with the shorter solution on its own `Ico 0 Tᵢ`: `velocity_unique_core`
  (U2) and `pressure_gauge_core` (U3) from `Uniqueness.lean`, whose conclusions
  live on `Ico 0 (min T₁ T₂)`, restricted along `Ico 0 Tᵢ ⊆ Ico 0 (min T₁ T₂)`
  via `Ico_subset_Ico le_rfl (le_min …)` and `PressureGaugeEquivOn.mono`.

Orientation notes:
* In the `T₁ ≤ T₂` branch the shorter one is `u₁`, so clause 1 needs
  `u₂.velocity = u₁.velocity`; `velocity_unique_core` gives `u₁ = u₂`, hence the
  `.symm`. Clause 3 needs `u₁.pressure ∼ u₂.pressure`, exactly `hpre`'s order, so
  no `.symm`.
* In the `T₂ ≤ T₁` branch it mirrors: clause 2 uses `hvel` directly, clause 4
  uses `hpre.symm`.

Helper lemmas added because D01/A02 does not carry them: `PressureGaugeEquivOn` is
reflexive / symmetric / monotone in the interval (all one-liners on the
`∃ c, ∀ t ∈ I, …` unfolding).

### U9 `lifespan_le_of_unbounded` — the field's norm is `L^∞`
**The field's chosen norm is `L^∞`**, not `H²`: `speedENorm z = eLpNorm z ⊤ volume`
(`Spec.lean:148-149`) and the blow-up hypothesis is
`limsupLeft T (fun t => speedENorm (u(t,·))) = ⊤` with
`limsupLeft T φ = Filter.limsup φ (𝓝[<] T)` (`Spec.lean:135-136`). Per the task's
instruction for the `L^∞` case, the proof uses the registered
`A03.bounded_representative` route through `Bounds.lean`'s
`ClassicalSolutionR.exists_velocity_bound` (U1b), **not** the `H²`-continuity/A03
manuscript sketch and **not** the `LocalizedBlowup.no_continuous_continuation`
fallback (which would need the strictly stronger *local* blow-up form on a compact
`K`, see COMPARISON §5.2).

Steps (by contradiction):
1. `not_le` + `exists_horizon_gt_of_lt_lifespan` (U6, `Order.lean`) → a solution
   `w` on some `T' > T`.
2. For each `t ∈ Ico 0 T`, pick `S = (t+T)/2 ∈ (0,T)`; the hypothesis gives `wS`
   with `wS.velocity = u`; `velocity_unique_core hν w wS` on
   `Ico 0 (min T' S) ∋ t` (since `t < S < T < T'`, so `min T' S = S`) identifies
   `w.velocity (t,·) = u (t,·)`. Gives `hagree` on all of `Ico 0 T`.
3. `w.exists_velocity_bound hT.le hTT'` (U1b) bounds `‖w.velocity (t,x)‖ ≤ B` on
   the compact `Icc 0 T ⊆ Ico 0 T'`; transport through `hagree`.
4. `speedENorm_le_ofReal`: a pointwise bound `‖z x‖ ≤ B` gives
   `eLpNorm z ⊤ volume ≤ ENNReal.ofReal B` via `eLpNorm_exponent_top` +
   `eLpNormEssSup_le_of_ae_bound (ae_of_all _ …)`.
5. `Ioo 0 T ∈ 𝓝[<] T` (as `Ioi 0 ∩ Iio T`, `Ioi 0 ∈ 𝓝 T` since `T > 0`), so the
   bound holds eventually; `Filter.limsup_le_of_le` (cobounded discharged by the
   `isBoundedDefault` autoparam — `ℝ≥0∞` is `OrderBot`) gives
   `limsupLeft T (…) ≤ ENNReal.ofReal B`.
6. `rw [hunbdd]` makes it `⊤ ≤ ENNReal.ofReal B`; `top_le_iff` +
   `ENNReal.ofReal_ne_top` closes `False`.

## Key Mathlib lemmas located (grep in `verification/.lake/packages/mathlib`)
* `MeasureTheory.eLpNormEssSup_le_of_ae_bound` (`LpSeminorm/Basic.lean:363`),
  `eLpNorm_exponent_top` (`LpSeminorm/Defs.lean:114`).
* `Filter.limsup_le_of_le` (`Order/LiminfLimsup.lean:140`) — cobounded autoparam.
* `Ioi_mem_nhds`, `mem_nhdsWithin_of_mem_nhds`, `self_mem_nhdsWithin`,
  `Set.Ioi_inter_Iio`, `Filter.eventually_of_mem`, `top_le_iff`.

## Approaches considered and rejected (no Lean dead-ends hit)
* **U5 via `ClassicalSolutionR.congr`/`exists_eq_fields_of_agree` gluing on the
  union** (Restrict.lean): unnecessary. The `max` of two reals *is* one of them,
  so the WLOG route is strictly shorter and needs no field-by-field
  reconstruction. Rejected before writing Lean.
* **U5 casting the witness with `hmax ▸ u₂`**: makes `(hmax ▸ u₂).velocity`
  a transported term rather than defeq `u₂.velocity`, so the `rfl` agreement
  clause would no longer close by `rfl`. Rewriting the *goal's* binder type with
  `rw [max_eq_right h]` keeps the witness literally `u₂`. This `rw` on an
  existential binder type type-checks (verified by build) because the body's
  occurrences reference `T₁`/`T₂`, never `max T₁ T₂`.
* **U9 via the `H²`-continuity + eq:Rproduct manuscript sketch (A03)**: would
  route through `sobolev` at order 2 and A03's embedding to an `L^∞` bound; the
  `Bounds.lean` `exists_velocity_bound` already packages exactly this delivery
  (A03 → jets → `L^∞`, `Bounds.lean` header sub-steps i–iv) as a pointwise
  velocity bound, so it is the same content, pre-assembled. Used directly.
* **U9 via `LocalizedBlowup.no_continuous_continuation`**: needs the *local*
  blow-up `LocalSpeedUnboundedAt T K u` on a compact `K`, strictly stronger than
  the contract's global `speedENorm`-`limsup = ⊤`. Not applicable to this
  statement's hypothesis. Fallback only, not used.

## Commands run
* `cd verification && lake build NSFormalization.Section4.A02.Patch` →
  `Built NSFormalization.Section4.A02.Patch (2.7s)`, `Build completed successfully`.
  (All warnings in the transcript are upstream replays; none on `Patch.lean`.)
* `cd verification && lake env lean ../research/A02/axioms_u5u9.lean` → the six
  `#print axioms` lines each print `[propext, Classical.choice, Quot.sound]`; both
  conformance `example`s elaborate with no error.
