import NSFormalization.Source.ForcedCylinderTranslation
import Euler.MeanOrbitSobolev

/-! Actual ordinary L2 descent of angle-invariant finite-order cylinder fields. -/
noncomputable section
namespace NSFormalization.Source.OrdinaryCylinderDescent
open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
open EulerSobolevPointEvaluation EulerMeanOrdinaryLift
open NSFormalization.Source.ForcedCylinderLocal
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Equality of L2 angle translates implies pointwise equality of the continuous H3 representative. -/
theorem representative_angle (u : SobolevSpace 1 3)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 3 (0, θ) u = u)
    (x : EulerSmoothLimit.Space) (θ : AddCircle (1 : ℝ)) :
    representative 1 u (x, θ) = representative 1 u (x, 0) := by
  have he (a : LiftDomain 1) (ha : sobolevTranslation 1 3 a u = u) :
      representative 1 u = fun z => representative 1 u (z + a) := by
    apply representative_eq 1 u _ ((representative_continuous 1 u).comp (continuous_id.add continuous_const))
    have ht := translation_ae 1 a (value 1 u)
    have hv : translation 1 a (value 1 u) = value 1 u := by
      rw [← translation_value, ha]
    rw [hv] at ht
    exact ht.trans ((measurePreserving_translation 1 a).quasiMeasurePreserving.ae (representative_ae 1 u))
  have h := congrFun (he (0, θ) (hu θ)) (x, 0)
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using h.symm

/-- An invariant actual finite-order field has an ordinary L2 preimage under the source lift. -/
theorem exists_ordinary_value {q : ℕ} (hq : 3 ≤ q) (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ∃ w : EulerMeanSolenoidal.L2, ordinaryLift w = value 1 u := by
  let v := restrictOperator 1 hq u
  have hv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 3 (0, θ) v = v := by
    intro θ
    dsimp [v]
    rw [← restrictOperator_translation, hu θ]
  let g : EulerSmoothLimit.Space → EulerSmoothLimit.Space := fun x => representative 1 v (x, 0)
  have hg : Continuous g := (representative_continuous 1 v).comp (continuous_id.prodMk continuous_const)
  have hae : (value 1 u : LiftDomain 1 → EulerSmoothLimit.Space) =ᵐ[liftMeasure 1]
      (g ∘ Prod.fst) := by
    have hr := representative_ae 1 v
    change (value 1 u : LiftDomain 1 → EulerSmoothLimit.Space) =ᵐ[liftMeasure 1] representative 1 v at hr
    exact hr.trans (Filter.Eventually.of_forall fun z => representative_angle v hv z.1 z.2)
  have hcomp : MemLp (g ∘ (Prod.fst : LiftDomain 1 → EulerSmoothLimit.Space)) 2 (liftMeasure 1) :=
    (memLp_congr_ae hae).mp (Lp.memLp (value 1 u))
  have hgLp : MemLp g 2 (volume : Measure EulerSmoothLimit.Space) := by
    have hm := (memLp_map_measure_iff hg.aestronglyMeasurable
      ordinaryProjection_measurePreserving.aemeasurable).mpr hcomp
    rwa [ordinaryProjection_measurePreserving.map_eq] at hm
  refine ⟨hgLp.toLp g, ?_⟩
  apply Lp.ext
  exact ((ordinaryLift_ae (hgLp.toLp g)).trans
    (ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae hgLp.coeFn_toLp)).trans hae.symm

/-- The ordinary observation is the existing lift adjoint composed with the actual value map. -/
def ordinaryValue (q : ℕ) : SobolevSpace 1 q →L[ℝ] EulerMeanSolenoidal.L2 :=
  ordinaryLift.toContinuousLinearMap.adjoint.comp (valueOperator 1 q)

/-- The adjoint observation reconstructs precisely those Hq inputs proved angle-invariant. -/
theorem ordinaryValue_lift {q : ℕ} (hq : 3 ≤ q) (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ordinaryLift (ordinaryValue q u) = value 1 u := by
  obtain ⟨w, hw⟩ := exists_ordinary_value hq u hu
  change ordinaryLift (ordinaryLift.toContinuousLinearMap.adjoint (value 1 u)) = value 1 u
  rw [← hw]
  have h := congrArg (fun M : EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2 => M w)
    ordinaryLift.adjoint_comp_self
  exact congrArg ordinaryLift h

/-- Existing ordinary Sobolev inputs satisfy every required angle-invariance condition. -/
theorem ordinarySobolev_angle (q : ℕ) (u : EulerMeanSolenoidal.L2)
    (hu : EulerMeanSmoothRepresentative.SmoothOrbit u) (θ : AddCircle (1 : ℝ)) :
    sobolevTranslation 1 q (0, θ) (EulerMeanSmoothRepresentative.ordinarySobolev q u hu) =
      EulerMeanSmoothRepresentative.ordinarySobolev q u hu := by
  apply value_injective 1
  rw [translation_value, EulerMeanSmoothRepresentative.ordinarySobolev_value,
    ordinaryLift_translation, EulerMeanSolenoidal.translation_zero]

end NSFormalization.Source.OrdinaryCylinderDescent
