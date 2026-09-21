import NSFormalization.Section4.A01.AprioriRows
import NSFormalization.Section4.A01.EulerPairing
import NSFormalization.Section4.A03.ScalarTameProduct

/-!
# A01 unit A3 row (i) — carrier-bridge words (a)(b)(c) discharging `hword_jet` (lane 151)

`research/A01/REVIEW_APRIORI_ROWS.md` §2 lists the four-part carrier-bridge lemma that discharges the
single named hypothesis `hword_jet` of lane 149's converse
(`AprioriRows.sobolevSpace_norm_le_sobolevENorm`):

```
hword_jet : ∀ n (hn : n ≤ q+1) (w : Fin n → Fin 4),
  ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
```

This module closes pieces **(a)**, **(b)**, **(c)** and assembles them into an **unconditional**
`hword_jet` bound for every order the descent reaches (`n + 3 ≤ q + 1`, i.e. `n ≤ q − 2`).  Only the
top three orders `n ∈ {q−1, q, q+1}` remain, on piece **(d)**.

## What is proved

* **(b) `eLpNorm_jet_component_le`** — the order-`n` Fréchet jet at the coordinate unit vectors
  `coordinateVector (w i)` has `L²` norm `≤ ‖iteratedFDeriv ℝ n z‖` in `L²`
  (`ContinuousMultilinearMap.le_opNorm`, `eLpNorm_mono`).
* **(c) `word_angular_eq_zero`** — for angle-invariant `u`, a derivative word whose leading direction
  is the **angular** one (`Fin.cons 0 w`, `standardDirection 0 = (0,1)`, defined at
  `vendor/NavierStokesAndEuler/Euler/EulerProof.lean:6529`) is `0`; ported from the reviewer probe
  `research/A01/probes/rev149_angular_words.lean`.
* **`word_eq_zero_of_mem_zero`** — the general form: a word with an angular slot in **any** position
  (`∃ k, w k = 0`) is `0` (leading slot is (c); a non-leading `0` vanishes by induction on the
  prefix).
* **(a) the descent helpers** `descent_step_ae` (inductive step), `wordField` / `wordField_field`
  (the iterated `SmoothL2Field.directionalField` word field and its classical Fréchet-jet identity),
  and `locInt_component_lp` / `locInt_component_smooth`.  The step's descent cancels the
  **complex-Schwartz** weak-derivative pairing (`weakDeriv_pairing_of_lift_hasDerivAt`, lane 140)
  against the classical field's own pairing (`D01.smoothField_weakDeriv_pairing`) through
  `A03.ae_eq_of_schwartz_pairing` (`Section4/A03/ScalarTameProduct.lean:136`).  These feed the
  full-order descent identity `word_descent_ae_full` in `L2Descent.lean` directly.

The restricted assembly `hword_jet_of_descent` and the descent identities `word_descent_ae` /
`word_descent_ae_partial` (all with `n + 3 ≤ q + 1`) were **retired** (lane 155): lane 153's
`L2Descent.hword_jet_full` / `word_descent_ae_full` prove the same statements for every `n ≤ q + 1`
and strictly subsume them (see the retirement note at the foot of this file).

## What was open, now closed

The top three orders `n ∈ {q−1, q, q+1}` — which `exists_descend` (`n + 3 ≤ q + 1`) could not reach —
are supplied by lane 153's `L2Descent.word_descent_ae_top` (the `L²`-level descent of the invariant
lift, no jet loss), so `hword_jet` is now discharged for every `n ≤ q + 1` in `L2Descent.lean`.

Downstream, a `ClassicalSolutionR` velocity slice supplies the `SmoothL2Field` carrier for free
(`D01.exists_smoothL2Field_of_memHInfty`, `DatumToJets.lean:306`), so the descent helpers'
`Z` and the review's `ContDiff ℝ ∞ z` form coincide there.

`#print axioms` is standard for every declaration (`research/A01/axioms_carrier_words.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open EulerLpTranslation
open NSFormalization.Source.OrdinaryCylinderDescent
open scoped ENNReal ContDiff LineDeriv

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## (b) The jet-component `L²` bound -/

/-- **(b).**  The order-`n` Fréchet jet of `z` evaluated at the coordinate unit vectors
`coordinateVector (w i)` has `L²` norm bounded by the full `L²` operator norm of `iteratedFDeriv ℝ n z`.
Pointwise this is `ContinuousMultilinearMap.le_opNorm` at unit inputs
(`∏ i, ‖coordinateVector (w i)‖ = 1`), lifted to `eLpNorm` by `eLpNorm_mono`. -/
theorem eLpNorm_jet_component_le (n : ℕ) (z : Space → Space) (w : Fin n → Fin 3) :
    eLpNorm (fun x => iteratedFDeriv ℝ n z x (fun i => coordinateVector (w i))) 2 volume
      ≤ eLpNorm (iteratedFDeriv ℝ n z) 2 volume := by
  refine eLpNorm_mono (fun x => ?_)
  calc ‖iteratedFDeriv ℝ n z x (fun i => coordinateVector (w i))‖
      ≤ ‖iteratedFDeriv ℝ n z x‖ * ∏ i, ‖coordinateVector (w i)‖ :=
        (iteratedFDeriv ℝ n z x).le_opNorm _
    _ = ‖iteratedFDeriv ℝ n z x‖ := by
        simp [coordinateVector]

/-! ## (c) Angular words vanish (port of `rev149_angular_words.lean`) -/

/-- **(c).**  Every derivative word whose **leading** direction is the angular one vanishes, for an
angle-invariant cylinder field.  Direction `0` of `Fin 4` is the circle direction
(`standardDirection 0 = (0,1)`); the orbit of the angle-invariant word `word 1 u hn.le w` is
constant, so its `0`-derivative is `0` (`HasDerivAt.unique` against `hasDerivAt_const`).  Ported from
the reviewer probe `research/A01/probes/rev149_angular_words.lean` (lane 149). -/
theorem word_angular_eq_zero {q n : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u)
    (hn : n < q) (w : Fin n → Fin 4) :
    word 1 u (Nat.succ_le_of_lt hn) (Fin.cons 0 w) = 0 := by
  have hword : ∀ θ : AddCircle (1 : ℝ),
      translation 1 (0, θ) (word 1 u hn.le w) = word 1 u hn.le w :=
    fun θ => congrArg (fun v : SobolevSpace 1 q => v.val ⟨⟨n, Nat.lt_succ_of_le hn.le⟩, w⟩) (hu θ)
  have hpath : ∀ t : ℝ,
      translationPath 1 (standardDirection 0) t = ((0 : Vector3), ((t : ℝ) : AddCircle (1 : ℝ))) := by
    intro t
    simp [translationPath, coveringMap, standardDirection_zero, Prod.smul_mk]
  have hderiv := word_hasDerivAt 1 u hn w 0
  have hfun : (fun t : ℝ =>
      translation 1 (translationPath 1 (standardDirection 0) t) (word 1 u hn.le w))
      = fun _ : ℝ => word 1 u hn.le w := by
    funext t
    rw [hpath t]
    exact hword ((t : ℝ) : AddCircle (1 : ℝ))
  rw [hfun] at hderiv
  exact ((hasDerivAt_const (0 : ℝ) (word 1 u hn.le w)).unique hderiv).symm

/-- **General angular vanishing.**  A derivative word of an angle-invariant cylinder field with an
angular slot in **any** position (`∃ k, w k = 0`) vanishes.  Induction on the length: leading `0` is
`word_angular_eq_zero`; a non-leading `0` puts a `0`-word in the tail, which vanishes by the
induction hypothesis, and differentiating the constant-`0` orbit gives `0`
(`word_hasDerivAt` + `HasDerivAt.unique`). -/
theorem word_eq_zero_of_mem_zero {q : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ∀ (n : ℕ) (hn : n ≤ q) (w : Fin n → Fin 4), (∃ k, w k = 0) → word 1 u hn w = 0 := by
  intro n
  induction n with
  | zero => rintro _ w ⟨k, _⟩; exact k.elim0
  | succ n ih =>
    intro hn w hex
    have hlt : n < q := hn
    by_cases hw0 : w 0 = 0
    · have key := word_angular_eq_zero u hu hlt (Fin.tail w)
      have hwc : Fin.cons (0 : Fin 4) (Fin.tail w) = w := by
        rw [← hw0]; exact Fin.cons_self_tail w
      rw [hwc] at key
      exact key
    · obtain ⟨k, hk⟩ := hex
      have hk0 : k ≠ 0 := by rintro rfl; exact hw0 hk
      obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.mpr hk0
      have htail : ∃ j, Fin.tail w j = 0 := ⟨k', hk⟩
      have hzero : word 1 u hlt.le (Fin.tail w) = 0 := ih hlt.le (Fin.tail w) htail
      have hderiv := word_hasDerivAt 1 u hlt (Fin.tail w) (w 0)
      have hconst : (fun t : ℝ => translation 1
          (translationPath 1 (standardDirection (w 0)) t) (word 1 u hlt.le (Fin.tail w)))
          = fun _ : ℝ => (0 : LiftL2 1) := by
        funext t; rw [hzero, map_zero]
      rw [hconst] at hderiv
      have hval := ((hasDerivAt_const (0 : ℝ) (0 : LiftL2 1)).unique hderiv).symm
      rw [Fin.cons_self_tail w] at hval
      exact hval

/-! ## (a) The descent-to-classical-jet a.e. identity

The descent (lane 140) delivers each word as a **strong `L²` translation-orbit derivative** at the
lift level; the identity with the ordinary-space classical Fréchet jet of the smooth velocity slice
is closed by cancelling the two complex-Schwartz weak-derivative pairings against each other through
`A03.ae_eq_of_schwartz_pairing`.  Folded from `research/A01/probes/rev151_descent_a_proved.lean`
(reviewer of lane 151). -/

/-- Local integrability of the `i`-th complex component of an ordinary `L²` field. -/
theorem locInt_component_lp (Z : EulerMeanSolenoidal.L2) (i : Fin 3) :
    LocallyIntegrable (fun x => ((Z x i : ℝ) : ℂ)) volume :=
  ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).comp_memLp'
    (Lp.memLp Z)).locallyIntegrable (by norm_num)

/-- Local integrability of the `i`-th complex component of a smooth `L²` field. -/
theorem locInt_component_smooth (Z : SmoothL2Field Space) (i : Fin 3) :
    LocallyIntegrable (fun x => ((Z.field x i : ℝ) : ℂ)) volume :=
  Continuous.locallyIntegrable (Complex.continuous_ofReal.comp
    (((EuclideanSpace.proj (𝕜 := ℝ) i)).continuous.comp Z.smooth.continuous))

/-- **(a), inductive step.**  If `⇑Zw` agrees a.e. with a smooth field `Z.field`, and the lift-level
strong derivative of `Zw`'s translation orbit in the `j`-th spatial direction is `ordinaryLift Zc`,
then `⇑Zc` agrees a.e. with the classical `j`-th directional derivative `(Z.directionalField eⱼ).field`.
The descent's complex-Schwartz pairing (`weakDeriv_pairing_of_lift_hasDerivAt`) and the smooth field's
own pairing (`D01.smoothField_weakDeriv_pairing`) are cancelled through `A03.ae_eq_of_schwartz_pairing`
componentwise. -/
theorem descent_step_ae (Z : SmoothL2Field Space) (j : Fin 3)
    (Zw Zc : EulerMeanSolenoidal.L2)
    (hZw : (⇑Zw) =ᵐ[volume] Z.field)
    (h : HasDerivAt (fun t : ℝ => EulerLiftedGradientSpace.translation 1
        (translationPath 1 (standardDirection j.succ) t) (ordinaryLift Zw)) (ordinaryLift Zc) 0) :
    (⇑Zc) =ᵐ[volume] (Z.directionalField (coordinateVector j)).field := by
  have key : ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space),
      ((Zc x i : ℝ) : ℂ) = (((Z.directionalField (coordinateVector j)).field x i : ℝ) : ℂ) := by
    intro i
    refine NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing (locInt_component_lp Zc i)
      (locInt_component_smooth (Z.directionalField (coordinateVector j)) i) ?_
    intro ψ
    have h1 := weakDeriv_pairing_of_lift_hasDerivAt j Zw Zc h i ψ
    have h2 := NSFormalization.Section4.D01.smoothField_weakDeriv_pairing Z j i ψ
    have h3 : ∫ x, (-∂_{coordinateVector j} ψ) x * ((Zw x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((Z.field x i : ℝ) : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [hZw] with x hx
      rw [hx]
    rw [h1, h3, ← h2]
  filter_upwards [ae_all_iff.mpr key] with x hx
  ext i
  exact_mod_cast hx i

/-- The iterated `SmoothL2Field.directionalField` word field. -/
def wordField (Z : SmoothL2Field Space) : ∀ {n : ℕ}, (Fin n → Fin 3) → SmoothL2Field Space
  | 0, _ => Z
  | (_ + 1), w => (wordField Z (Fin.tail w)).directionalField (coordinateVector (w 0))

/-- The word field is the classical Fréchet-jet slice at the coordinate directions
(`iteratedFDeriv_succ_apply_left`). -/
theorem wordField_field (Z : SmoothL2Field Space) :
    ∀ (n : ℕ) (w : Fin n → Fin 3) (x : Space),
      (wordField Z w).field x = iteratedFDeriv ℝ n Z.field x (fun i => coordinateVector (w i))
  | 0, w, x => by simp [wordField, iteratedFDeriv_zero_apply]
  | (n + 1), w, x => by
      have hd : HasFDerivAt (iteratedFDeriv ℝ n Z.field)
          (fderiv ℝ (iteratedFDeriv ℝ n Z.field) x) x :=
        (Z.smooth.differentiable_iteratedFDeriv (m := n)
          (by exact_mod_cast WithTop.coe_lt_top _) x).hasFDerivAt
      set E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) Space
        (fun i => coordinateVector ((Fin.tail w) i)) with hE
      have hcomp : HasFDerivAt (fun y => iteratedFDeriv ℝ n Z.field y
          (fun i => coordinateVector ((Fin.tail w) i)))
          (E.comp (fderiv ℝ (iteratedFDeriv ℝ n Z.field) x)) x :=
        E.hasFDerivAt.comp x hd
      have hfun : (wordField Z (Fin.tail w)).field
          = fun y => iteratedFDeriv ℝ n Z.field y (fun i => coordinateVector ((Fin.tail w) i)) :=
        funext fun y => wordField_field Z n (Fin.tail w) y
      show fderiv ℝ (wordField Z (Fin.tail w)).field x (coordinateVector (w 0)) = _
      rw [hfun, hcomp.fderiv, iteratedFDeriv_succ_apply_left]
      simp only [hE, ContinuousMultilinearMap.apply_apply, ContinuousLinearMap.coe_comp,
        Function.comp_apply]
      rfl

/-! ## Retired: `word_descent_ae`, `word_descent_ae_partial`, `hword_jet_of_descent`

These three carried the `n + 3 ≤ q + 1` order restriction (spatial words only up to `n ≤ q − 2`).
Lane 153's `L2Descent.word_descent_ae_full` / `hword_jet_full` (`Section4/A01/L2Descent.lean`) prove
the same identities for **every** `n ≤ q + 1`, so they strictly subsume the three and reduce to them
by restriction (`research/A01/probes/rev153_subsumes.lean`).  Having two `hword_jet` suppliers with
different order hypotheses invited miscitation, so the restricted versions were retired here (lane
155, `research/A01/REVIEW_L2_DESCENT.md` §N3).  The helpers above (`wordField`, `wordField_field`,
`descent_step_ae`, `word_eq_zero_of_mem_zero`, `eLpNorm_jet_component_le`, `locInt_component_*`) stay:
the `L2Descent` full versions are built directly on them. -/

end NSFormalization.Section4.A01
