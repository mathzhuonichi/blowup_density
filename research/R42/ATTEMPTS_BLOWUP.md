# R42 split item #2a — `blowup_essSup` (lane 080)

Module: `formalization/NSFormalization/Section4/R42/BlowupEssSup.lean`
(imports only `NSFormalization.Section4.A02.Patch`).

Discharges the pointwise → `L^∞` (essential-supremum) step of
`research/R42/LIFESPAN_SPLIT.md` section "(#2) `blowup_essSup`", i.e. residual
(2a) there. Two theorems + one slice-continuity helper; the pointwise predicate
`SpeedUnboundedAt` is **reused** (not restated) — see finding 1 below.

> Revised after lane-080 review (`research/R42/REVIEW_BLOWUP.md`, verdict
> ACCEPT-WITH-NOTES): findings 1 (delete duplicate `SpeedUnboundedAt`), 2 (drop
> `_hT`), 3 (add `continuous_slice_of_velocity_smooth`), 5 (fix axioms-file comment)
> applied.

## What was proved

* `ofReal_le_eLpNormTop_of_continuous` (S) — a continuous field attaining
  `M < ‖z x‖` has `ENNReal.ofReal M ≤ eLpNorm z ⊤ volume`.
* `limsupLeft_speedENorm_eq_top` (M) — `SpeedUnboundedAt T u` + slice continuity
  on `(0,T)` ⟹ `A02.limsupLeft T (fun t => A02.speedENorm (u(t,·))) = ⊤`.
* `continuous_slice_of_velocity_smooth` — `ContDiffOn ℝ ∞ u (Ico 0 T ×ˢ univ)` ⟹
  `∀ t ∈ Ioo 0 T, Continuous (u(t,·))` — the exact `hcont` input of Lemma 2 from the
  exact `InsertionFamilyAPI.velocity_smooth` shape. Derivation credited to the
  lane-080 reviewer (`REVIEW_BLOWUP.md`, finding 3).

`SpeedUnboundedAt` is the pre-existing canonical local copy
`NSFormalization.Source.PacketScaling.SpeedUnboundedAt` (`Source/PacketScaling.lean:22`),
reachable with the module's single import, opened via
`open NSFormalization.Source.PacketScaling`; it is character-identical to
`verification/Contracts/V1/Scaling.lean:124` and already `rfl`-bridged in
`verification/Bindings/Scaling.lean:50`. No new bridge is needed.

## Route (as executed) and exact Mathlib names used

Lemma 1 `ofReal_le_eLpNormTop_of_continuous`:
1. `eLpNorm_exponent_top` then `eLpNormEssSup_eq_essSup_enorm`
   (`Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean:80`) rewrite the goal to
   `ofReal M ≤ essSup (fun y => ‖z y‖ₑ) volume`.
2. `by_contra` + `not_lt` ⟹ `essSup … < ofReal M`; `ae_lt_of_essSup_lt`
   (`Mathlib/MeasureTheory/Function/EssSup.lean:248`; side goal auto by
   `isBoundedDefault`, ℝ≥0∞ has `OrderTop`) gives `‖z y‖ₑ < ofReal M` a.e.
3. `{y | M < ‖z y‖}` is open by `isOpen_lt continuous_const hz.norm`, nonempty
   (contains `x`), so positive measure by `IsOpen.measure_pos`
   (`Mathlib/MeasureTheory/Measure/OpenPos.lean:47`; `μ` is EXPLICIT: call
   `hopen.measure_pos volume ⟨x, hx⟩`). The instance
   `MeasureTheory.Measure.IsOpenPosMeasure (volume : Measure Space)` resolves
   automatically for `Space = EuclideanSpace ℝ (Fin 3)` (verified `by infer_instance`).
4. That open set `⊆ {y | ¬ ‖z y‖ₑ < ofReal M}` via `ENNReal.ofReal_le_ofReal` and
   `ofReal_norm` (`Mathlib/Analysis/Normed/Group/Basic.lean`; `ofReal ‖a‖ = ‖a‖ₑ`).
5. `ae_iff.mp hae` makes the superset null; `measure_mono` + `not_le.mpr hpos`
   contradicts positivity.

Lemma 2 `limsupLeft_speedENorm_eq_top`:
1. `by_contra` + `lt_top_iff_ne_top` ⟹ limsup `< ⊤`; `exists_between`
   (ℝ≥0∞ `DenselyOrdered`) picks `b` with `limsup < b < ⊤`.
2. Frequently statement via `(nhdsLT_basis T).frequently_iff.mpr`
   (`nhdsLT_basis`, `Mathlib/Topology/Order/LeftRightNhds.lean:234`:
   `(𝓝[<] T).HasBasis (· < T) (Ioo · T)`; ℝ is `NoMinOrder`) — used `.mpr`
   (not `rw`) to sidestep higher-order predicate unification.
3. For `c < T`: apply `hblow (b.toReal+1) _ (T-c) _`; `htc : T-(T-c) < t` gives
   `c < t` (`linarith`), `ht.2 : t < T`, so `t ∈ Ioo c T`.
4. Lemma 1 (with `hcont t ht` and `hMx`) gives `ofReal (b.toReal+1) ≤ speedENorm`;
   `b = ofReal b.toReal` (`ENNReal.ofReal_toReal hb2.ne`) `≤ ofReal (b.toReal+1)`
   (`ENNReal.ofReal_le_ofReal`), so `b ≤ speedENorm`.
5. `le_limsup_of_frequently_le'` (`Mathlib/Order/LiminfLimsup.lean:517`, CompleteLattice,
   no cobounded side condition) gives `b ≤ limsup`, contradicting `limsup < b`
   (`absurd hle (not_le.mpr hb1)`).

Helper `continuous_slice_of_velocity_smooth` (reviewer's finding-3 derivation):
`hu.continuousOn` restricted (`ContinuousOn.mono`) to the *open* box
`Ioo 0 T ×ˢ univ` (`isOpen_Ioo.prod isOpen_univ`, `Set.prod_mono Ioo_subset_Ico_self`)
gives `ContinuousAt u (t,x)` at interior points (`ContinuousOn.continuousAt` +
`IsOpen.mem_nhds`), then `.comp` with the continuous `y ↦ (t,y)` (`fun_prop`). `Ioo`
(not `Ico`) is essential: at `t = 0` only `ContinuousWithinAt` holds.

`A02.limsupLeft`/`A02.speedENorm` are used through their definitional unfolding
(the `def` bodies are literally `Filter.limsup φ (nhdsWithin T (Iio T))` and
`eLpNorm z ⊤ volume`), so Lemma-1's `eLpNorm` conclusion and the
`le_limsup_of_frequently_le'` `Filter.limsup` conclusion typecheck against the
`A02.*` names by defeq — no rewrite needed.

## Failed / abandoned approaches (recorded negative examples)

* **Duplicate-predicate mistake (review finding 1).** The first draft *restated*
  `SpeedUnboundedAt` as a new local `def`, with the ATTEMPTS note "no local copy
  existed in `Section4/{I03,R42,A02}`". That is literally true but the wrong
  conclusion: the grep was **scoped to `Section4/` only**. `Source/` (where the
  contract's own docstring points, `Contracts/V1/Scaling.lean:118-123`) already had
  the canonical `NSFormalization.Source.PacketScaling.SpeedUnboundedAt`
  (`Source/PacketScaling.lean:22`), character-identical and already `rfl`-bridged
  (`Bindings/Scaling.lean:50`), and reachable with the module's single import.
  **Lesson: always grep `Source/` and `Paper3/` too, not just `Section4/`.** The
  duplicate was a "本地重述只允许一份" violation and a silent-shadow risk
  (`Assembly.lean` opens both `R42` and `PacketScaling`). Fix: delete the `def`, add
  `open NSFormalization.Source.PacketScaling`; the two theorem statements stay
  token-identical (`SpeedUnboundedAt T u` now resolves to the PacketScaling copy,
  verified by `#check`).
* `le_antisymm … (zero_le _)` to get `volume {..} = 0`: **failed** —
  `error: Function expected at zero_le … 0 ≤ ?m` (the ambient resolution of
  `zero_le` in the ℝ≥0∞ goal produced a term of type `0 ≤ ?m` with no explicit
  slot, so `zero_le _` is a mis-application). Replaced by contradicting the
  already-proved `hpos : 0 < volume {..}` directly:
  `absurd ((measure_mono hsub).trans hzero.le) (not_le.mpr hpos)`. Cleaner, no
  `zero_le`/`le_zero_iff` name hunt.
* `simp only [mem_setOf_eq, not_lt]`: built, but emitted a deprecation warning
  (`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`). Replaced with defeq
  `have hy' : M < ‖z y‖ := hy` + `show ¬ …` + `rw [not_lt]`, keeping the module
  warning-free.
* task-suggested basis names `nhdsWithin_Iio_basis'` / `Filter.HasBasis.nhdsWithin_Iio`:
  **not present** in this Mathlib rev (grep empty). Correct name is `nhdsLT_basis`.
* task-suggested `Filter.limsup_eq_top_iff` / `ENNReal.limsup_eq_top_iff`:
  **not present** by those names; used the `∀ b < ⊤, b ≤ limsup` route via
  `exists_between` + `le_limsup_of_frequently_le'` instead.
* `hT : 0 < T` on Lemma 2 (review finding 2): the first draft kept it (as `_hT`)
  arguing "the A02 consumer supplies it". **Wrong on both counts** — the consumer
  `lifespan_le_of_unbounded` carries its own `0 < T` at its boundary and gains
  nothing from a second copy, and `0 < T` is *derivable* from `hblow`
  (`obtain ⟨t, x, ht, _, _⟩ := hblow 1 one_pos 1 one_pos; exact ht.1.trans ht.2`).
  The hypothesis is genuinely unused in the proof (the filter `𝓝[<] T` is `NeBot`
  on ℝ regardless of sign). Fix: **dropped entirely**, making the lemma strictly
  easier to apply and removing an `_`-placeholder from a public signature.

## Gap

None for item #2a. Both of clause #2's inputs to `limsupLeft_speedENorm_eq_top`
now have a clean supply for the R42 assembly lane:
* the raw `SpeedUnboundedAt family.T (velocity ε)` is `InsertionFamilyAPI.blowup`
  (`Contracts/V1/InsertionFamily.lean:304`) — binding-layer plumbing, no new math;
* the slice-continuity `hcont` is now one application of the in-module
  `continuous_slice_of_velocity_smooth` to `InsertionFamilyAPI.velocity_smooth`
  (`InsertionFamily.lean:196`).

## Commands / results (after review fixes)

* `lake build NSFormalization.Section4.R42.BlowupEssSup` → `✔ Built` (2.7s),
  `Build completed successfully (9943 jobs)`.
* `lake env lean …/BlowupEssSup.lean` → silent (no warnings, no errors).
* `lake env lean …/research/R42/axioms_blowup.lean` → all three public decls
  (`ofReal_le_eLpNormTop_of_continuous`, `limsupLeft_speedENorm_eq_top`,
  `continuous_slice_of_velocity_smooth`) → `[propext, Classical.choice, Quot.sound]`.
* `#check` confirms Lemma 2's hypothesis is `Source.PacketScaling.SpeedUnboundedAt`
  (no duplicate) and `_hT` is gone.
* `make check` → contract-policy 13/13 OK, work queue 30 items consistent,
  architecture checks pass.
