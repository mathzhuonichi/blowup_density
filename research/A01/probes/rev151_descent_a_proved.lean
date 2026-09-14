import NSFormalization.Section4.A01.CarrierWords
import NSFormalization.Section4.A03.ScalarTameProduct

/-! # Reviewer probe (lane 151): piece **(a)** `word_descent_ae_partial`, PROVED.

The lane's records say (a) is an L-level open problem blocked by a signature mismatch
(descent gives *complex Schwartz* pairings, Mathlib's uniqueness takes *real compactly supported*
test functions, "not in the tree").  The bridge **is** in the tree:
`NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing`
(`formalization/NSFormalization/Section4/A03/ScalarTameProduct.lean:136`) consumes exactly the
complex-Schwartz `∫ ψ x * f x` pairing and already performs the complex→real and
Schwartz→compact-support conversions internally.

This file proves (a) in full from tree lemmas only:
* `descent_step_ae` — the inductive step, from `A01.weakDeriv_pairing_of_lift_hasDerivAt` (lane 140)
  and `D01.smoothField_weakDeriv_pairing` (`FiniteOrderConstructor.lean:306`) through
  `A03.ae_eq_of_schwartz_pairing`;
* `wordField` / `wordField_field` — the iterated `SmoothL2Field.directionalField` word field is the
  classical jet slice (`iteratedFDeriv_succ_apply_left`);
* `word_descent_ae` / `word_descent_ae'` — the induction on the word length, base case = `⇑U =ᵐ z`.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`.  See
`research/A01/REVIEW_CARRIER_WORDS.md` §3. -/

noncomputable section
namespace Rev151A

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open EulerLpTranslation
open NSFormalization.Section4.A01
open scoped ENNReal ContDiff LineDeriv

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem locInt_lp (Z : EulerMeanSolenoidal.L2) (i : Fin 3) :
    LocallyIntegrable (fun x => ((Z x i : ℝ) : ℂ)) volume :=
  ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).comp_memLp'
    (Lp.memLp Z)).locallyIntegrable (by norm_num)

theorem locInt_smooth (Z : SmoothL2Field Space) (i : Fin 3) :
    LocallyIntegrable (fun x => ((Z.field x i : ℝ) : ℂ)) volume :=
  Continuous.locallyIntegrable (Complex.continuous_ofReal.comp
    (((EuclideanSpace.proj (𝕜 := ℝ) i)).continuous.comp Z.smooth.continuous))

/-- **Step.**  From the descent's complex-Schwartz pairing and the smooth field's own pairing. -/
theorem descent_step_ae (Z : SmoothL2Field Space) (j : Fin 3)
    (Zw Zc : EulerMeanSolenoidal.L2)
    (hZw : (⇑Zw) =ᵐ[volume] Z.field)
    (h : HasDerivAt (fun t : ℝ => EulerLiftedGradientSpace.translation 1
        (translationPath 1 (standardDirection j.succ) t) (ordinaryLift Zw)) (ordinaryLift Zc) 0) :
    (⇑Zc) =ᵐ[volume] (Z.directionalField (coordinateVector j)).field := by
  have key : ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space),
      ((Zc x i : ℝ) : ℂ) = (((Z.directionalField (coordinateVector j)).field x i : ℝ) : ℂ) := by
    intro i
    refine NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing (locInt_lp Zc i)
      (locInt_smooth (Z.directionalField (coordinateVector j)) i) ?_
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

/-- The iterated directional-derivative field of a word. -/
def wordField (Z : SmoothL2Field Space) : ∀ {n : ℕ}, (Fin n → Fin 3) → SmoothL2Field Space
  | 0, _ => Z
  | (_ + 1), w => (wordField Z (Fin.tail w)).directionalField (coordinateVector (w 0))

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

/-- **(a), in full.**  The descent-to-classical-jet a.e. identity for spatial words. -/
theorem word_descent_ae {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field) :
    ∀ (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 3) (Zw : EulerMeanSolenoidal.L2),
      ordinaryLift Zw = word 1 u (by omega) (fun i => (w i).succ) →
      (⇑Zw) =ᵐ[volume] (wordField Z w).field := by
  intro n
  induction n with
  | zero =>
    intro hn w Zw hZw
    have hwemp : (fun i => ((w : Fin 0 → Fin 3) i).succ) = (Fin.elim0 : Fin 0 → Fin 4) :=
      Subsingleton.elim _ _
    have hval : word 1 u (by omega : (0:ℕ) ≤ q + 1) (fun i => (w i).succ) = value 1 u := by
      rw [hwemp]; rfl
    have hZU : Zw = U := ordinaryLift.injective (by rw [hZw, hval, hU])
    subst hZU
    exact hUz
  | succ n ih =>
    intro hn w Zw hZw
    have hlt : n < q + 1 := by omega
    have hn' : n + 3 ≤ q + 1 := by omega
    obtain ⟨Zw', hZw'⟩ := exists_descend u hu (fun i => ((Fin.tail w) i).succ)
      (by omega) (by omega)
    have hIH := ih hn' (Fin.tail w) Zw' hZw'
    have hcons : Fin.cons ((w 0).succ) (fun i => ((Fin.tail w) i).succ)
        = fun i => (w i).succ := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro k; simp [Fin.tail]
    have hderiv := word_hasDerivAt 1 u hlt (fun i => ((Fin.tail w) i).succ) ((w 0).succ)
    rw [hcons] at hderiv
    rw [← hZw', ← hZw] at hderiv
    have := descent_step_ae (wordField Z (Fin.tail w)) (w 0) Zw' Zw hIH hderiv
    exact this

/-- (a) in the review's `iteratedFDeriv` form. -/
theorem word_descent_ae' {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field)
    (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 3) (Zw : EulerMeanSolenoidal.L2)
    (hZw : ordinaryLift Zw = word 1 u (by omega) (fun i => (w i).succ)) :
    (⇑Zw) =ᵐ[volume] fun x => iteratedFDeriv ℝ n Z.field x (fun i => coordinateVector (w i)) := by
  have h := word_descent_ae u hu U hU Z hUz n hn w Zw hZw
  refine h.trans (Filter.EventuallyEq.of_eq ?_)
  funext x
  exact wordField_field Z n w x

end Rev151A
