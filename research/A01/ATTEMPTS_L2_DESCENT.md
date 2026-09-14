# ATTEMPTS — lane 153 (A01 · piece (d): the L²-level descent of an angle-invariant lift)

Module: `formalization/NSFormalization/Section4/A01/L2Descent.lean` (namespace
`NSFormalization.Section4.A01`). New file only; **no existing module edited**. Imports
`Section4.A01.CarrierWords` (lane 151), which transitively gives `AprioriRows`, `EulerPairing`,
`A03.ScalarTameProduct`, and the vendor lift/descent stack.

Target: the last open piece **(d)** of `research/A01/REVIEW_APRIORI_ROWS.md` §2 / the lane-151
`CarrierWords.lean` docstring — the `L²`-level descent that covers the top three orders
`n ∈ {q−1, q, q+1}` that the jet-level `exists_descend` (which needs `n + 3 ≤ q + 1`) never reaches.

## What is proved (all 4 decls 3-axiom, `research/A01/axioms_l2_descent.lean`)

1. **`exists_ordinaryLift_of_invariant`** — piece (d), exactly `DescentL2` of
   `research/A01/probes/probe151_descent_L2.lean`:
   ```
   (g : LiftL2 1) (hginv : ∀ θ : AddCircle (1:ℝ), translation 1 ((0:Vector3), θ) g = g) :
     ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g
   ```
2. **`word_descent_ae_top`** — item 2(a). For all `n ≤ q + 1` (no jet loss):
   ```
   (u : SobolevSpace 1 (q+1)) (hu : ∀ θ, sobolevTranslation 1 (q+1) (0,θ) u = u)
     (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 3) :
     ∃ Zw : EulerMeanSolenoidal.L2, ordinaryLift Zw = word 1 u hn (fun i => (w i).succ)
   ```
3. **`word_descent_ae_full`** — the descent-to-classical-jet a.e. identity of
   `CarrierWords.word_descent_ae`, with the `n + 3 ≤ q + 1` restriction **removed** (all `n ≤ q+1`):
   ```
   (u) (hu) (U) (hU : ordinaryLift U = value 1 u) (Z : SmoothL2Field Space)
     (hUz : ⇑U =ᵐ[volume] Z.field)
     (n) (hn : n ≤ q + 1) (w : Fin n → Fin 3) (Zw) (hZw : ordinaryLift Zw = word 1 u hn (fun i => (w i).succ)) :
     ⇑Zw =ᵐ[volume] (wordField Z w).field
   ```
4. **`hword_jet_full`** — item 2(b), the `hword_jet` bound for **all** `n ≤ q + 1`, unconditional:
   ```
   (u) (hu) (U) (hU) (Z) (hUz) :
     ∀ (n) (hn : n ≤ q + 1) (w : Fin n → Fin 4),
       ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n Z.field) 2 volume).toReal
   ```
   Combined with lane 151's `hword_jet_of_descent` this discharges lane 149's single named hypothesis
   `hword_jet` (`AprioriRows.sobolevSpace_norm_le_sobolevENorm`) for **every** order.

## The route that closed (d): averaging / Fubini, NOT Fourier

The 151 review sketched a Fourier-Hilbert-basis route (kill nonzero `AddCircle` modes). I closed (d)
with a **shorter, Fourier-free averaging route** that folds "angle-invariant `L²` ⇒ a.e. constant"
into the product argument, so no standalone circle lemma is needed.

`EulerMeanSolenoidal.L2 = Lp Space 2 volume`, `LiftL2 1 = Lp Vector3 2 (liftMeasure 1)` with
`liftMeasure 1 = (volume : Measure Vector3).prod (volume : Measure (AddCircle 1))` (def). Steps:

* **Strongly-measurable representative** `g₀` of `g`: `(Lp.aestronglyMeasurable g).mk`,
  `.stronglyMeasurable_mk`, `.ae_eq_mk`. (Needed so the graph set below is genuinely measurable.)
* **a.e. angular invariance of `g₀`**: `translation_ae 1 (0,θ) g` + `hginv θ` give
  `⇑g =ᵐ fun x => ⇑g (x + (0,θ))`; transport to `g₀` on both sides using
  `(measurePreserving_translation 1 (0,θ)).quasiMeasurePreserving.ae hg₀ae`.
* **Quantifier swap** `∀ θ, ∀ᵐ x` → `∀ᵐ x, ∀ᵐ θ`: `Measure.ae_ae_comm` (weakening `∀ θ` to `∀ᵐ θ`
  via `ae_of_all`), whose measurability side condition is
  `measurableSet_eq_fun (g₀∘snd) (g₀∘(fun z => z.2+(0,z.1)))` — `MeasurableEq Vector3` holds because
  `Vector3` is second-countable + T2 (`BorelSpace/Basic.lean:620`).
* **Slice constancy** for a.e. `pt`: with `G₀ x := ∫ θ, g₀ (x,θ) ∂volume`,
  ```
  g₀ pt = ∫ g₀ pt              (integral_const, IsProbabilityMeasure volume on AddCircle 1)
        = ∫ g₀ (pt+(0,θ))      (integral_congr_ae, a.e. invariance of the slice)
        = ∫ g₀ (pt.1, pt.2+θ)  (pt+(0,θ) = (pt.1, pt.2+θ), Prod.add_def + add_zero)
        = ∫ g₀ (pt.1, θ)       (integral_add_left_eq_self, Haar/IsAddLeftInvariant volume)
        = G₀ pt.1
  ```
  This step is where invariance ⇒ constancy is discharged, with no integrability side conditions
  (each equality is unconditional).
* **`G₀ ∈ L²(volume)`**: `⇑g =ᵐ G₀∘fst` (from `hg₀ae` + slice constancy), so
  `MemLp (G₀∘fst) 2 (liftMeasure 1) = (Lp.memLp g).ae_eq …`; then
  `memLp_map_measure_iff` (with `AEStronglyMeasurable.integral_prod_right'` for `G₀`) through
  `ordinaryProjection_measurePreserving.map_eq : map fst (liftMeasure 1) = volume` gives
  `MemLp G₀ 2 volume`.
* **Assemble**: `G := (MemLp G₀).toLp`; `ordinaryLift G = g` by `Lp.ext` from
  `ordinaryLift_ae` + `MemLp.coeFn_toLp` + slice constancy.

Item 2 reuses lane-151 helpers unchanged (`descent_step_ae`, `wordField`, `wordField_field`,
`word_eq_zero_of_mem_zero`, `eLpNorm_jet_component_le`, `word_hasDerivAt`). The word-invariance of a
spatial word is the same `congrArg (fun v => v.val ⟨⟨n,_⟩, fun i => (w i).succ⟩) (hu θ)` that
`exists_descend`'s `hinv` uses (`sobolevTranslation` acts by `translation` on each derivative
coordinate — `liftOperator_apply`, which is `rfl`). `word_descent_ae_full` is `CarrierWords`'s
`word_descent_ae` induction verbatim with the single line `exists_descend u hu … (by omega) (by omega)`
replaced by `word_descent_ae_top u hu n hn' (Fin.tail w)`; nothing else in that induction used the
order bound (`descent_step_ae` and `word_hasDerivAt` need only `n < q+1`).

## Mathlib lemmas used (verified by `research/A01/probes/probe153_sigs.lean`, `probe153_micro.lean`)

`Measure.ae_ae_comm`, `integral_add_left_eq_self` (to_additive; Haar
translation invariance — `#check`ed, not greppable), `memLp_map_measure_iff`,
`measurableSet_eq_fun` (with `MeasurableEq Vector3`),
`integral_const` + `IsProbabilityMeasure`, `Lp.aestronglyMeasurable(.mk/.ae_eq_mk/.stronglyMeasurable_mk)`,
`MemLp.ae_eq`, `MemLp.coeFn_toLp`, `Lp.memLp`, `MeasurePreserving.map_eq`, `Lp.ext`; vendor
`translation_ae`, `measurePreserving_translation`, `ordinaryLift_ae`, `ordinaryLift_translation`,
`ordinaryProjection_measurePreserving`, `liftOperator_apply`, `word_hasDerivAt`.
(`Measure.ae_ae_of_ae_prod` and `AEStronglyMeasurable.integral_prod_right'` were only `#check`ed in the
sigs probe; the module does not use them — review 153 N2.)

## Failed / rejected approaches

* **`rw [show pt + (0,θ) = (pt.1, pt.2+θ) from …]` directly inside `integral_congr_ae`** — the goal
  carried un-reduced β-redexes `(fun θ => g₀ (pt+(0,θ))) θ = (fun θ => g₀ (pt.1, pt.2+θ)) θ`:
  ```
  Tactic `rewrite` failed: Did not find an occurrence of the pattern
    pt + (0, θ)
  in the target expression
    (fun θ => g₀ (pt + (0, θ))) θ = (fun θ => g₀ (pt.1, pt.2 + θ)) θ
  ```
  Fix: a `show g₀ (pt + (0,θ)) = g₀ (pt.1, pt.2 + θ)` first to β-reduce, then the `rw`.
* **`fun_prop` for `Measurable (fun z => g₀ (z.2 + (0, z.1)))`** — failed
  (`fun_prop was unable to prove Measurable ?m`) on the malformed nested composition. Fix: build the
  inner map explicitly, `measurable_snd.add (measurable_const.prodMk measurable_fst)`, then
  `hg₀sm.measurable.comp`.
* **The Fourier route (151 review's recommendation)** — viable, but rejected as heavier: it works on
  `AddCircle → ℂ` slices (each of 3 real components complexified), kills nonzero `fourierCoeff`, and
  still ends at the same `G₀ = ∫` mean + the same `MemLp G₀` / `ordinaryLift G₀ = g` obligations. The
  averaging route reaches the same slice-constancy through `ae_ae_comm` + `integral_add_left_eq_self`
  with no Fourier machinery. Recorded here as the alternative, not tried to completion.
* **Standalone lemma "an `Lp` `AddCircle` function invariant under all translations is a.e.
  constant"** — the brief allowed isolating this if ≤ 60 lines. It proved **unnecessary**: the
  averaging chain above discharges invariance ⇒ constancy inline (the `integral_congr_ae` +
  `integral_add_left_eq_self` two-liner), so no separate circle lemma was stated.

## Status against row (i)

Row (i)'s four-part carrier bridge ((a)(b)(c) in lane 151, (d) here) is **complete**. With
`word_descent_ae_top` + `word_descent_ae_full` + `hword_jet_full`, lane 149's `hword_jet` is
discharged for **all** `n ≤ q + 1` (lane 151 covered `n ≤ q − 2`; this lane adds `n ∈ {q−1,q,q+1}`).
The remaining A01 residuals for `HasAprioriBound` are the non-carrier rows: (iv) angle invariance
`hinv`, the `T₀ = T` Grönwall endpoint, and the datum/forcing restart spine (row (v)).
