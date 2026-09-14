import NSFormalization.Section4.D01.FiniteOrderConstructor
import NSFormalization.Section4.A01.CarrierBridge
import Euler.LpSmoothApproximation
import Euler.MeanSolenoidalTranslation
import Euler.MeanOrdinaryLift
import Euler.CylinderSobolevSpace
import NSFormalization.Source.OrdinaryCylinderDescent

/-!
# The Euler-side Schwartz pairing for the finite-order carrier bridge (unit A01 · D-euler-pairing)

`research/D01/FINITE_ORDER_SPLIT.md` closed the D01 side of C1b-m-D (the finite-order angular Sobolev
datum constructor `NSFormalization.Section4.D01.exists_isSobolevDatum_of_memLp_derivs`, whose
hypothesis is the iterated Schwartz-pairing weak-derivative predicate `HasWeakDerivsL2`).  The one
remaining external obligation is row **D-euler-pairing**: the Euler side owes the Schwartz-pairing
form of the weak derivatives that the cylinder solution delivers as *strong `L²` translation
derivatives* (`Euler/CylinderSobolevSpace.word_hasDerivAt`).

## What is proved here

* `weakDeriv_pairing_of_translation_hasDerivAt` (**row D-euler-pairing / C1b-m-E's E2, the real
  obligation**).  For ordinary `L²` fields `z`, `w` such that `w` is the *strong `L²` derivative* of
  the spatial translation orbit of `z` in direction `eⱼ` (`HasDerivAt (fun t => translation (t•eⱼ) z)
  w 0`, exactly the shape `Euler/CylinderSobolevSpace.word_hasDerivAt` produces), the weak-derivative
  Schwartz pairing `∫ ψ·wᵢ = ∫ (−∂ⱼψ)·zᵢ` holds for every complex Schwartz test function `ψ` and
  every component `i` — in the exact pairing shape `HasWeakDerivsL2` consumes.  No smoothness of `z`;
  the only differentiation is of the smooth orbit of `ψ`, moved onto `ψ` by translation invariance of
  Lebesgue measure.

* `exists_isSobolevDatum_m_ordinaryL2` (**row C1b-m-D payoff**).  An Euler ordinary `L²` field `U`
  with `L²` weak derivatives up to order `m` (`HasWeakDerivsL2 (⇑U) m`) has an order-`m` angular
  real-vector Sobolev datum — one `exact` on D01's finite-order constructor.

* `exists_isSobolevDatum_m_of_ae` (**row C1b-rep transport**).  Its `IsSobolevDatum.congr_field`
  transport onto any velocity field `v` agreeing with `⇑U` a.e. (the B1 hand-off shape used by
  `DatumPathContinuity.datumPath_isSobolevDatum`).

## Order budget and the horizon caveat (from `research/D01/REVIEW_FINITE_ORDER_CLOSE.md` §6)

`Source.OrdinaryForcedLocal.exists_local {q} (hq : 6 ≤ q)` fixes its horizon `T` **after** `q`, and
descending each derivative word costs three Sobolev orders (`exists_ordinary_value` needs `3 ≤ r`).
So the chain delivers `HasWeakDerivsL2 (⇑(U t)) m` for `m ≤ q − 3` on the interval `T = T(q)` — i.e.
each finite order `m` on its **own** horizon, not all orders on one horizon.
`exists_isSobolevDatum_m_ordinaryL2` then fires at every `t ∈ [0,T(q)]` for that `m`, which is C1b-m-D
as stated.  A common `T` for all `m` (`MemHInfty` strength) needs a `q`-independent horizon —
persistence of regularity, which is A3's obligation, not D-euler-pairing's.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/A01/axioms_euler_pairing.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.A01

open MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space coordinateVector)
open scoped LineDeriv SchwartzMap ComplexConjugate

/-! ## 0. Component-projection continuous linear map

`complexComponentCLM i` sends an ordinary `L²` field to the `L²` function `x ↦ (field x)ᵢ` viewed as
a complex-valued `L²` element — the composite of the `i`-th Euclidean coordinate projection with the
real-to-complex embedding, lifted to `Lp`. -/

/-- The `i`-th coordinate of an ordinary `L²` field, cast to `ℂ`, as an `L²`-valued continuous linear
map. -/
def complexComponentCLM (i : Fin 3) :
    EulerMeanSolenoidal.L2 →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  ContinuousLinearMap.compLpL 2 (volume : Measure Space)
    (Complex.ofRealCLM.comp (EuclideanSpace.proj i))

theorem coeFn_complexComponentCLM (i : Fin 3) (v : EulerMeanSolenoidal.L2) :
    ((complexComponentCLM i v : Lp ℂ 2 (volume : Measure Space)) : Space → ℂ) =ᵐ[volume]
      fun x => ((v x i : ℝ) : ℂ) := by
  simp only [complexComponentCLM]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) v] with x hx
  rw [hx]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  rfl

/-! ## 1. E2 — strong `L²` translation derivative ⟹ Schwartz weak-derivative pairing

This is row **D-euler-pairing** (`research/D01/FINITE_ORDER_SPLIT.md`).  The heartbeat budget below is
for elaborating the single composed statement (the two pairing functionals are `innerSL`-composites of
`Lp` continuous linear maps); the proof itself does no heartbeat-heavy search. -/

set_option maxHeartbeats 400000 in
/-- **Row D-euler-pairing (E2): the real obligation.**  If `w` is the strong `L²` derivative at `0`
of the spatial translation orbit `t ↦ translation (t•eⱼ) z` of an ordinary `L²` field `z` — exactly
the datum `Euler/CylinderSobolevSpace.word_hasDerivAt` supplies for a descended derivative word — then
`w` is the weak `j`-th derivative of `z` in the Schwartz-pairing sense `∫ ψ·wᵢ = ∫ (−∂ⱼψ)·zᵢ`, for
every complex Schwartz `ψ` and component `i`.  This is the exact pairing shape consumed by
`NSFormalization.Section4.D01.HasWeakDerivsL2`.

The proof pairs both sides against a fixed test object through the `L²` inner product: the left side
is the composite of the (continuous linear) pairing functional with the given strong-derivative path;
the right side moves the translation onto `ψ` by translation invariance of Lebesgue measure and
differentiates the smooth `L²` orbit of `ψ` (`EulerLpTranslation.smooth_hasFDerivAt`, needing only
`ψ, ∂ⱼψ ∈ L²`).  The two scalar functions coincide, so their derivatives at `0` agree.  No smoothness
of `z`, no dominated-convergence bound, no compact cutoff. -/
theorem weakDeriv_pairing_of_translation_hasDerivAt (j : Fin 3)
    {z w : EulerMeanSolenoidal.L2}
    (h : HasDerivAt (fun t : ℝ => EulerMeanSolenoidal.translation (t • coordinateVector j) z) w 0)
    (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * ((w x i : ℝ) : ℂ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ) := by
  classical
  set Ci := complexComponentCLM i with hCidef
  have hLp : MemLp (⇑ψ) 2 (volume : Measure Space) := ψ.memLp 2
  have hconj : MemLp (fun x => conj (ψ x)) 2 (volume : Measure Space) :=
    hLp.congr_norm ((Complex.continuous_conj.comp ψ.continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => (Complex.norm_conj (ψ x)).symm)
  set psiC : Lp ℂ 2 (volume : Measure Space) := hconj.toLp _ with hpsiCdef
  have hDLp : MemLp (fderiv ℝ (⇑ψ)) 2 (volume : Measure Space) := by
    have he : (fderiv ℝ (⇑ψ)) = ⇑(SchwartzMap.fderivCLM ℝ Space ℂ ψ) := by
      funext x; simp only [SchwartzMap.fderivCLM_apply]
    rw [he]; exact (SchwartzMap.fderivCLM ℝ Space ℂ ψ).memLp 2
  set P : EulerMeanSolenoidal.L2 →L[ℝ] ℂ :=
    ((innerSL ℂ psiC).restrictScalars ℝ).comp Ci with hPdef
  set Qz : Lp ℂ 2 (volume : Measure Space) →L[ℝ] ℂ :=
    (innerSL ℂ (Ci z)).restrictScalars ℝ with hQzdef
  have hPval : ∀ v, P v = (inner ℂ psiC (Ci v) : ℂ) := by
    intro v
    simp only [hPdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      innerSL_apply_apply]
  have hQval : ∀ φ, Qz φ = (inner ℂ (Ci z) φ : ℂ) := by
    intro φ
    simp only [hQzdef, ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply]
  have hP : ∀ v : EulerMeanSolenoidal.L2,
      (inner ℂ psiC (Ci v) : ℂ) = ∫ x, ψ x * ((v x i : ℝ) : ℂ) := by
    intro v
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hconj.coeFn_toLp, coeFn_complexComponentCLM i v] with x hpc hcv
    rw [hpc, hcv, RCLike.inner_apply]
    simp only [starRingEnd_apply, star_star]
    ring
  have hQ : ∀ φ : Lp ℂ 2 (volume : Measure Space),
      (inner ℂ (Ci z) φ : ℂ) = ∫ x, φ x * ((z x i : ℝ) : ℂ) := by
    intro φ
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_complexComponentCLM i z] with x hcz
    rw [hcz, RCLike.inner_apply, Complex.conj_ofReal]
  have hFD := EulerLpTranslation.smooth_hasFDerivAt (⇑ψ) (ψ.smooth (⊤ : ℕ∞)) hLp hDLp
  set Dfull := EulerLpDerivative.derivativeMap (volume : Measure Space)
    (hDLp.toLp (fderiv ℝ (⇑ψ))) with hDfulldef
  have hv : HasDerivAt (fun t : ℝ => t • (-coordinateVector j)) (-coordinateVector j) 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const (-coordinateVector j)
  have hσ0 := hFD.comp_hasDerivAt_of_eq (0 : ℝ) hv (by simp)
  set Dψ := Dfull (-coordinateVector j) with hDψdef
  have hσ : HasDerivAt
      (fun t : ℝ => EulerLpTranslation.translation (t • (-coordinateVector j)) (hLp.toLp (⇑ψ)))
        Dψ 0 := by
    simpa only [Function.comp_def] using hσ0
  have hDψ_ae : (Dψ : Space → ℂ) =ᵐ[volume] fun x => (-∂_{coordinateVector j} ψ) x := by
    filter_upwards [EulerLpDerivative.derivativeMap_ae (volume : Measure Space)
        (hDLp.toLp (fderiv ℝ (⇑ψ))) (-coordinateVector j), hDLp.coeFn_toLp] with x hx hcoe
    have hlhs : (Dψ : Space → ℂ) x = -((fderiv ℝ (⇑ψ) x) (coordinateVector j)) := by
      rw [hDψdef, hx, hcoe, map_neg]
    rw [hlhs, ← SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rfl
  have hcov : ∀ t : ℝ, (∫ x, ψ x * ((z (x + t • coordinateVector j) i : ℝ) : ℂ))
      = ∫ x, ψ (x - t • coordinateVector j) * ((z x i : ℝ) : ℂ) := by
    intro t
    have key := integral_add_right_eq_self (μ := (volume : Measure Space))
      (fun x => ψ (x - t • coordinateVector j) * ((z x i : ℝ) : ℂ)) (t • coordinateVector j)
    simpa only [add_sub_cancel_right] using key
  have hσ_ae : ∀ t : ℝ,
      ((EulerLpTranslation.translation (t • (-coordinateVector j)) (hLp.toLp (⇑ψ)) :
        Lp ℂ 2 (volume : Measure Space)) : Space → ℂ)
        =ᵐ[volume] fun x => ψ (x - t • coordinateVector j) := by
    intro t
    have h1 := EulerLpTranslation.translation_ae (t • (-coordinateVector j)) (hLp.toLp (⇑ψ))
    have h2 := (measurePreserving_add_right (volume : Measure Space)
      (t • (-coordinateVector j))).quasiMeasurePreserving.ae hLp.coeFn_toLp
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
    congr 1
    rw [smul_neg]; abel
  have hGL : (fun t => P (EulerMeanSolenoidal.translation (t • coordinateVector j) z))
      = fun t : ℝ => ∫ x, ψ x * ((z (x + t • coordinateVector j) i : ℝ) : ℂ) := by
    funext t
    rw [hPval, hP]
    refine integral_congr_ae ?_
    filter_upwards [EulerMeanSolenoidal.translation_ae (t • coordinateVector j) z] with x hx
    rw [hx]
  have hGR : (fun t => Qz (EulerLpTranslation.translation (t • (-coordinateVector j)) (hLp.toLp (⇑ψ))))
      = fun t : ℝ => ∫ x, ψ x * ((z (x + t • coordinateVector j) i : ℝ) : ℂ) := by
    funext t
    rw [hQval, hQ, hcov t]
    refine integral_congr_ae ?_
    filter_upwards [hσ_ae t] with x hx
    rw [hx]
  have hGfun_L : HasDerivAt
      (fun t : ℝ => ∫ x, ψ x * ((z (x + t • coordinateVector j) i : ℝ) : ℂ)) (P w) 0 := by
    have hc := P.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simp only [Function.comp_def] at hc
    rwa [hGL] at hc
  have hGfun_R : HasDerivAt
      (fun t : ℝ => ∫ x, ψ x * ((z (x + t • coordinateVector j) i : ℝ) : ℂ)) (Qz Dψ) 0 := by
    have hc := Qz.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hσ
    simp only [Function.comp_def] at hc
    rwa [hGR] at hc
  have hPw : P w = ∫ x, ψ x * ((w x i : ℝ) : ℂ) := by rw [hPval, hP]
  have hQD : Qz Dψ = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ) := by
    rw [hQval, hQ]
    refine integral_congr_ae ?_
    filter_upwards [hDψ_ae] with x hx
    rw [hx]
  rw [← hPw, ← hQD]
  exact hGfun_L.unique hGfun_R

/-! ## 1b. E1 linchpin — descending the cylinder strong derivative to the ordinary `L²` carrier

`Euler/CylinderSobolevSpace.word_hasDerivAt` supplies the strong `L²` translation derivative at the
*lifted cylinder* level (`EulerLiftedGradientSpace.translation` along `translationPath`).  The next
lemma pulls that derivative back through the isometric embedding `ordinaryLift` to the ordinary `L²`
translation orbit that E2 consumes.  The pullback uses that `ordinaryLift` intertwines the two
translations (`EulerMeanOrdinaryLift.ordinaryLift_translation`) with the spatial component of
`translationPath 1 (standardDirection j.succ) t` equal to `t • coordinateVector j`, and that
`ordinaryLift` has a continuous linear left inverse (`LinearIsometry.adjoint_comp_self`). -/

open EulerMeanOrdinaryLift EulerLiftedGradientSpace EulerCylinderSobolev
  EulerPressureSpatialRegularity in
/-- **E1 linchpin.**  If, at the lifted cylinder level, the strong `L²` derivative at `0` of the
translation orbit of `ordinaryLift Zw` along the `j`-th spatial direction is `ordinaryLift Zc`, then
`Zc` is the strong `L²` derivative at `0` of the ordinary spatial translation orbit of `Zw` in
direction `eⱼ`.  This is the shape produced by `Euler/CylinderSobolevSpace.word_hasDerivAt` (for
`ordinaryLift`-descended derivative words), converted to the shape `E2` consumes. -/
theorem hasDerivAt_meanTranslation_of_lift (j : Fin 3) (Zw Zc : EulerMeanSolenoidal.L2)
    (h : HasDerivAt (fun t : ℝ => EulerLiftedGradientSpace.translation 1
        (translationPath 1 (standardDirection j.succ) t) (ordinaryLift Zw)) (ordinaryLift Zc) 0) :
    HasDerivAt (fun t : ℝ => EulerMeanSolenoidal.translation (t • coordinateVector j) Zw) Zc 0 := by
  have hfun : (fun t : ℝ => EulerLiftedGradientSpace.translation 1
        (translationPath 1 (standardDirection j.succ) t) (ordinaryLift Zw))
      = fun t : ℝ => ordinaryLift (EulerMeanSolenoidal.translation (t • coordinateVector j) Zw) := by
    funext t
    have hfst : (translationPath 1 (standardDirection j.succ) t).1 = t • coordinateVector j := by
      simp [translationPath, coveringMap, standardDirection_succ, coordinateVector]
    rw [ordinaryLift_translation, hfst]
  rw [hfun] at h
  set A := ContinuousLinearMap.adjoint ordinaryLift.toContinuousLinearMap with hA
  have hAL : ∀ x : EulerMeanSolenoidal.L2, A (ordinaryLift x) = x := by
    intro x
    have hc := congrArg (fun M : EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2 => M x)
      (LinearIsometry.adjoint_comp_self ordinaryLift)
    simpa only [hA, ContinuousLinearMap.comp_apply, one_apply_eq_self,
      LinearIsometry.coe_toContinuousLinearMap] using hc
  have hcomp := A.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [Function.comp_def, hAL] at hcomp
  exact hcomp

open EulerMeanOrdinaryLift EulerLiftedGradientSpace EulerCylinderSobolev
  EulerPressureSpatialRegularity in
/-- **E1 → E2 chained.**  A single-step Euler weak-derivative Schwartz pairing directly from the
lift-level strong derivative: if `ordinaryLift Zc` is the lifted-cylinder strong `L²` derivative of
the `j`-th spatial translation orbit of `ordinaryLift Zw`, then `Zc` is the weak `j`-th derivative of
`Zw` in the Schwartz-pairing sense.  Composes `hasDerivAt_meanTranslation_of_lift` with
`weakDeriv_pairing_of_translation_hasDerivAt`.  This is what the (remaining) per-word descent feeds
into `HasWeakDerivsL2`. -/
theorem weakDeriv_pairing_of_lift_hasDerivAt (j : Fin 3) (Zw Zc : EulerMeanSolenoidal.L2)
    (h : HasDerivAt (fun t : ℝ => EulerLiftedGradientSpace.translation 1
        (translationPath 1 (standardDirection j.succ) t) (ordinaryLift Zw)) (ordinaryLift Zc) 0)
    (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * ((Zc x i : ℝ) : ℂ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((Zw x i : ℝ) : ℂ) :=
  weakDeriv_pairing_of_translation_hasDerivAt j (hasDerivAt_meanTranslation_of_lift j Zw Zc h) i ψ

/-! ## 1c. E1 — descending every derivative word and assembling `HasWeakDerivsL2`

The abstract cylinder solution value `u : SobolevSpace 1 (q+1)` of
`Source.OrdinaryForcedLocal.exists_local` is angle-invariant (its clause 7) and carries strong `L²`
spatial derivatives to order `q+1` (`word`).  `exists_descend` sends each derivative word of order
`≤ q − 2` to an ordinary `L²` field via the source lift adjoint (`exists_ordinary_value`), where the
angle-invariance of the packaged jet collapses — through `value_injective` — to the angle-invariance
of the word itself.  `hasWeakDerivsL2_of_word` then assembles `HasWeakDerivsL2` by induction on the
order, descending each successive coordinate derivative word and feeding the lift-level
`word_hasDerivAt` through `weakDeriv_pairing_of_lift_hasDerivAt`. -/

section Descent

open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open NSFormalization.Source.OrdinaryCylinderDescent NSFormalization.Source.ForcedCylinderLocal

/-- **E1 descent.**  A coordinate derivative word `w` (length `n`) of an angle-invariant cylinder
Sobolev field `u`, with three orders of regularity to spare (`n + 3 ≤ q`), descends to an ordinary
`L²` field `Zw` with `ordinaryLift Zw = word 1 u _ w`.  The regularity is packaged as a depth-`3` jet
(`word_has_jet` → `ofJet`), whose angle-invariance reduces by `value_injective` to that of the word
(hence of `u`), and the source lift adjoint (`exists_ordinary_value`) produces the ordinary
preimage. -/
theorem exists_descend {q n : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u)
    (w : Fin n → Fin 4) (hn : n ≤ q) (hnq : n + 3 ≤ q) :
    ∃ Zw : EulerMeanSolenoidal.L2, ordinaryLift Zw = word 1 u hn w := by
  obtain ⟨J⟩ := word_has_jet 1 u 3 n hnq w
  have hinv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 3 (0, θ) (ofJet 1 J) = ofJet 1 J := by
    intro θ
    apply value_injective 1
    rw [translation_value, value_ofJet]
    exact congrArg (fun v : SobolevSpace 1 q => v.val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩) (hu θ)
  obtain ⟨Zw, hZw⟩ := exists_ordinary_value (le_refl 3) (ofJet 1 J) hinv
  exact ⟨Zw, by rw [hZw, value_ofJet]⟩

/-- **E1 assembly (row C1b-m-E / D-euler-pairing).**  If `Zw` descends the length-`n` word `w` of an
angle-invariant cylinder field `u`, and `w` has `m` further orders of regularity to spare
(`n + m + 3 ≤ q`), then the ordinary `L²` representative `⇑Zw` has `L²` weak derivatives to order `m`
in the exact `HasWeakDerivsL2` sense.  By induction on `m`: the base case is `Zw ∈ L²`; the step
descends each coordinate derivative word `Fin.cons j.succ w`, applies the induction hypothesis to it,
and supplies the Schwartz pairing by pulling `word_hasDerivAt` back through `ordinaryLift`
(`weakDeriv_pairing_of_lift_hasDerivAt`). -/
theorem hasWeakDerivsL2_of_word {q : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ∀ (m n : ℕ) (hn : n ≤ q) (_hnm : n + m + 3 ≤ q) (w : Fin n → Fin 4)
      (Zw : EulerMeanSolenoidal.L2), ordinaryLift Zw = word 1 u hn w →
      HasWeakDerivsL2 (⇑Zw) m
  | 0, _n, _hn, _hnm, _w, Zw, _ => Lp.memLp Zw
  | (k + 1), n, hn, hnm, w, Zw, hZw => by
      refine ⟨Lp.memLp Zw, fun j => ?_⟩
      have hlt : n < q := by omega
      have hn1 : n + 1 ≤ q := hlt
      obtain ⟨Zc, hZc⟩ := exists_descend u hu (Fin.cons j.succ w) hn1 (by omega)
      refine ⟨⇑Zc, ?_, ?_⟩
      · exact hasWeakDerivsL2_of_word u hu k (n + 1) hn1 (by omega) (Fin.cons j.succ w) Zc hZc
      · intro i ψ
        have hderiv := word_hasDerivAt 1 u hlt w j.succ
        have e1 : word 1 u hlt.le w = ordinaryLift Zw := hZw.symm
        have e2 : word 1 u (Nat.succ_le_of_lt hlt) (Fin.cons j.succ w) = ordinaryLift Zc := hZc.symm
        rw [e1, e2] at hderiv
        exact weakDeriv_pairing_of_lift_hasDerivAt j Zw Zc hderiv i ψ

/-- **E1 top level (from the cylinder solution).**  For the order-`(q+1)` cylinder solution value `u`
of `Source.OrdinaryForcedLocal.exists_local` (angle-invariant, clause 7) whose ordinary observation
`U` satisfies `ordinaryLift U = value 1 u` (clause 4), the representative `⇑U` has `L²` weak
derivatives to every order `m ≤ q − 2` (`m + 3 ≤ q + 1`) in the `HasWeakDerivsL2` sense. -/
theorem hasWeakDerivsL2_of_cylinder {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m + 3 ≤ q + 1) :
    HasWeakDerivsL2 (⇑U) m := by
  refine hasWeakDerivsL2_of_word u hu m 0 (Nat.zero_le _) (by omega) Fin.elim0 U ?_
  rw [hU]; rfl

/-- **C1b-m-D on the actual cylinder solution.**  Combining `hasWeakDerivsL2_of_cylinder` with D01's
finite-order constructor: the ordinary `L²` observation `U` of the order-`(q+1)` cylinder solution `u`
carries an order-`m` angular real-vector Sobolev datum for every `m ≤ q − 2`.  (The horizon caveat of
the module header applies: `T` from `exists_local` depends on `q`.) -/
theorem exists_isSobolevDatum_m_of_cylinder {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m + 3 ≤ q + 1) :
    ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (⇑U) A :=
  exists_isSobolevDatum_of_memLp_derivs m (⇑U) (hasWeakDerivsL2_of_cylinder u hu U hU m hm)

end Descent

/-! ## 2. The payoff — C1b-m-D on the Euler ordinary `L²` carrier

Given the Euler-facing hypothesis `HasWeakDerivsL2 (⇑U) m` (which the descended cylinder derivative
words supply via E2), D01's finite-order constructor produces the order-`m` datum directly. -/

/-- **Row C1b-m-D payoff.**  An Euler ordinary `L²` field `U` whose representative has `L²` weak
derivatives up to order `m` (`HasWeakDerivsL2 (⇑U) m`) carries an order-`m` angular real-vector
Sobolev datum.  This is `NSFormalization.Section4.D01.exists_isSobolevDatum_of_memLp_derivs`
specialised to the ordinary `L²` carrier `⇑U`. -/
theorem exists_isSobolevDatum_m_ordinaryL2 (m : ℕ) (U : EulerMeanSolenoidal.L2)
    (hU : HasWeakDerivsL2 (⇑U) m) :
    ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (⇑U) A :=
  exists_isSobolevDatum_of_memLp_derivs m (⇑U) hU

/-- **Row C1b-rep transport.**  The order-`m` datum of `⇑U` transfers to any physical velocity field
`v` agreeing with `⇑U` a.e. (the B1 hand-off `velocity t =ᵐ ⇑(U t)`), by `IsSobolevDatum.congr_field`
— the same move `DatumPathContinuity.datumPath_isSobolevDatum` uses at order `0`. -/
theorem exists_isSobolevDatum_m_of_ae (m : ℕ) (U : EulerMeanSolenoidal.L2) (v : Space → Space)
    (hv : v =ᵐ[volume] ⇑U) (hU : HasWeakDerivsL2 (⇑U) m) :
    ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) v A := by
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_m_ordinaryL2 m U hU
  exact ⟨A, IsSobolevDatum.congr_field hA hv.symm⟩

end NSFormalization.Section4.A01
