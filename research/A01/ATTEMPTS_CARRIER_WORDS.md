# ATTEMPTS — lane 151 (A01 · carrier-bridge words (a)(b)(c) for `hword_jet`)

Module: `formalization/NSFormalization/Section4/A01/CarrierWords.lean` (namespace
`NSFormalization.Section4.A01`).  New file only; no existing module edited.  Imports
`AprioriRows` (lane 149), `EulerPairing` (lane 140), `A03.ScalarTameProduct` (the fundamental-lemma
bridge).

Target: discharge lane 149's single named hypothesis
`hword_jet : ∀ n (hn : n ≤ q+1) (w : Fin n → Fin 4), ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal`
of `AprioriRows.sobolevSpace_norm_le_sobolevENorm`, via the four-part carrier bridge of
`research/A01/REVIEW_APRIORI_ROWS.md` §2, statements (a)–(d).

> **Post-review correction (lane 151 review N1, `research/A01/REVIEW_CARRIER_WORDS.md`).**  An earlier
> version of this file recorded piece **(a)** as an L-level open problem "not in the tree" (a
> signature mismatch: descent gives complex-Schwartz pairings, Mathlib's uniqueness takes real
> compactly-supported test functions).  **That was wrong.**  The bridge *is* a tree theorem,
> `NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing` (`Section4/A03/ScalarTameProduct.lean:136`),
> which consumes the complex-Schwartz `∫ ψ x * f x` pairing directly and does the complex→real and
> Schwartz→compact-support conversions internally.  (a) is now **proved and landed**.  This is
> LESSONS line 3 again: grep every namespace before declaring "not in the tree".

## What is proved (module `CarrierWords.lean`), all 3-axiom

1. **(b) `eLpNorm_jet_component_le (n) (z) (w : Fin n → Fin 3)`** — the jet component at unit vectors
   has `L²` norm `≤ eLpNorm (iteratedFDeriv ℝ n z)` (`ContinuousMultilinearMap.le_opNorm`, `∏ = 1`,
   `eLpNorm_mono`).
2. **(c) `word_angular_eq_zero`** (port of `rev149_angular_words.lean`) **and** `word_eq_zero_of_mem_zero`
   — a word with an angular slot in *any* position (`∃ k, w k = 0`) is `0` (`standardDirection 0 = (0,1)`
   is `vendor/NavierStokesAndEuler/Euler/EulerProof.lean:6529`).
3. **(a) `word_descent_ae_partial`** (+ `descent_step_ae`, `wordField`, `wordField_field`,
   `word_descent_ae`, and helpers `locInt_component_lp`/`locInt_component_smooth`) — **the
   descent-to-classical-jet a.e. identity, fully proved.**  For a smooth `L²` slice
   `Z : SmoothL2Field Space` with `⇑U =ᵐ Z.field`, a spatial word `w : Fin n → Fin 3` with
   `n + 3 ≤ q + 1`, and `Zw` descending it:
   `⇑Zw =ᵐ fun x => iteratedFDeriv ℝ n Z.field x (fun i => coordinateVector (w i))`.  Route:
   * `descent_step_ae` — the inductive step.  The descent's complex-Schwartz pairing
     (`weakDeriv_pairing_of_lift_hasDerivAt`, lane 140) and the smooth field's own pairing
     (`D01.smoothField_weakDeriv_pairing`, `FiniteOrderConstructor.lean:306`) are cancelled through
     `A03.ae_eq_of_schwartz_pairing`, componentwise (`Fin 3`, then `EuclideanSpace.ext` a.e. via
     `ae_all_iff`).  No IBP against a non-compactly-supported test function is performed, so LESSONS'
     094 trap is not entered.
   * `wordField` / `wordField_field` — the iterated `SmoothL2Field.directionalField` word field is
     the classical Fréchet-jet slice (`iteratedFDeriv_succ_apply_left`,
     `ContinuousMultilinearMap.apply`).
   * `word_descent_ae` / `word_descent_ae_partial` — induction on the word length; base case
     `⇑U =ᵐ Z.field` (empty word descends to `U`, `ordinaryLift.injective`).
   Folded from the reviewer's `research/A01/probes/rev151_descent_a_proved.lean`.
4. **`hword_jet_of_descent`** — the assembly, now **unconditional**.  From `(u, hu, U, hU, Z, hUz)`:
   for every `w : Fin n → Fin 4` with `n + 3 ≤ q + 1`,
   `‖word 1 u _ w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n Z.field) 2 volume).toReal`.  Angular words are `0`
   (`word_eq_zero_of_mem_zero`, `ENNReal.toReal_nonneg`); spatial words `w i = (w' i).succ` by
   `exists_descend` (lane 140) + (a) + (b) through `ordinaryLift.norm_map`/`Lp.norm_def`/
   `eLpNorm_congr_ae`.  The `.toReal` finiteness `eLpNorm (iteratedFDeriv ℝ n Z.field) 2 ≠ ⊤` is
   **free** from `Z.integrable n` (a `SmoothL2Field` carries `MemLp` jets at all orders) — no `hfin`
   hypothesis is needed.

Exact final statements:

```
theorem word_descent_ae_partial {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ, sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field)
    (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 3) (Zw : EulerMeanSolenoidal.L2)
    (hZw : ordinaryLift Zw = word 1 u (by omega) (fun i => (w i).succ)) :
    (⇑Zw) =ᵐ[volume] fun x => iteratedFDeriv ℝ n Z.field x (fun i => coordinateVector (w i))

theorem hword_jet_of_descent {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ, sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field) :
    ∀ (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 4),
      ‖word 1 u (by omega) w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n Z.field) 2 volume).toReal
```

The smooth slice is carried as `Z : SmoothL2Field Space` rather than the review's bare
`(hz : ContDiff ℝ ∞ z)` because `D01.smoothField_weakDeriv_pairing` is stated on that carrier; it is
free downstream via `D01.exists_smoothL2Field_of_memHInfty` (`DatumToJets.lean:306`) — a
`ClassicalSolutionR` velocity slice has smooth + all-order `L²` jets — so the review's `ContDiff` form
is a corollary.

Conformance `research/A01/axioms_carrier_words.lean`: all 11 declarations `#print axioms` =
`[propext, Classical.choice, Quot.sound]`; non-vacuity on `u = 0`, `U = 0`, `Z = zeroField`,
exercising the unconditional assembly (hence (a)+(b)) end-to-end.

## The one remaining open piece

### (d) `L²`-level descent of the invariant lift — top three orders (open)

`hword_jet_of_descent` covers `n + 3 ≤ q + 1`, i.e. `n ≤ q − 2`.  The top three orders
`n ∈ {q−1, q, q+1}` never descend (`exists_descend` needs `n + 3 ≤ q + 1`), so they need piece (d):
`∀ g : LiftL2 1, (∀ θ, translation 1 (0,θ) g = g) → ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g`
(stated as a `Prop`, no proof, in `research/A01/probes/probe151_descent_L2.lean`).

* **Why the jet-level descent loses 3 orders:** `exists_ordinary_value`
  (`Source/OrdinaryCylinderDescent.lean:29`) descends by taking the **θ = 0 slice of the continuous
  H³ representative** `representative 1 v (x, 0)` — a pointwise function; that slice is the 3-order
  jet loss (`3 ≤ q`).  A raw `LiftL2 1` element has no pointwise θ = 0 slice.
* **The route (review N-`(d)`):** `EulerMeanSolenoidal.L2 = Lp Space 2 volume` carries **no**
  solenoidal/mean constraint at this level, so (d) is only a disintegration.
  `LiftL2 1 = Lp Vector3 2 (liftMeasure 1)` with
  `liftMeasure 1 = (volume : Measure Vector3).prod (volume : Measure (AddCircle 1))`
  (`EulerProof.lean:1092`) — a genuine product measure on `ℝ³ × S¹`.  Usable tool: the `AddCircle`
  Fourier Hilbert basis `fourierBasis` (`Mathlib/Analysis/Fourier/AddCircle.lean:411`,
  `span_fourierLp_closure_eq_top` at `:261`): angle invariance forces every nonzero-mode coefficient
  to vanish (`ĝ_k(x)·e^{2πikθ₀} = ĝ_k(x)` for all `θ₀`), leaving the `k = 0` mode `= G ∘ Prod.fst`;
  `ordinaryLift_ae` + `ordinaryProjection_measurePreserving` then close it, Fubini for the slice-wise
  `MemLp` being standard.  (Mathlib's `Dynamics/Ergodic/AddCircleAdd.lean` is about a *single*
  irrational rotation and is the wrong tool — the invariance here is under the whole circle action.)
  Still an L-ish piece, but the ingredient list is concrete.

## Status against row (i)

After this lane, discharging `hword_jet` for **all `n ≤ q − 2` is unconditional** ((a)(b)(c)
assembled), and the only remaining obstacle to lane 149's converse `hword_jet` is (d), the top three
orders.  The consumer `AprioriRows.sobolevSpace_norm_le_sobolevENorm` also still needs `hu` (angle
invariance) and the smooth-slice hand-off `(U, hU, hUz, Z)`, which a `ClassicalSolutionR` supplies
downstream.

## Failed / rejected approaches

* **Recording (a) as "not in the tree / L-level" after grepping only
  `ae_eq_of_integral_contDiff_smul_eq`** (Mathlib, real compact support): wrong — the complex-Schwartz
  form `A03.ae_eq_of_schwartz_pairing` exists (`ScalarTameProduct.lean:136`) and wraps the
  real/compact conversions.  Correct move (LESSONS 3): grep the *statement shape* across all
  namespaces (`grep -rn 'ae_eq.*schwartz\|schwartz.*pairing' formalization vendor`), not one lemma
  name.
* **Rewriting the whole word `w` with `rw [hwc]`** where `hwc : w = Fin.cons (w 0) (Fin.tail w)`: `rw`
  also rewrites the `w` inside `Fin.tail w`.  Fix: rewrite the *hypothesis* term
  (`rw [Fin.cons_self_tail w] at hval`, atomic RHS).
* **`push_neg at hex`**: deprecated in this Lean (`Prefer using push Not`), breaks `lake env lean`
  silence.  Fix: `have hne : ∀ i, w i ≠ 0 := fun i hi => hex ⟨i, hi⟩`.
* **`simp [coordinateVector, EuclideanSpace.norm_single]`** in (b): the RCLike `EuclideanSpace.norm_single`
  is not what simp fires (the `PiLp` one is in the default set) — "unused simp argument".  Fix:
  `simp [coordinateVector]`.
* **Carrying `hfin : sobolevENorm (q+1) z ≠ ⊤` as an assembly hypothesis** (the lane-149-style
  finiteness): unnecessary once the slice is a `SmoothL2Field` — `Z.integrable n` gives
  `eLpNorm (iteratedFDeriv ℝ n Z.field) 2 ≠ ⊤` directly.
