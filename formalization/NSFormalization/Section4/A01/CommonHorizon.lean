import NSFormalization.Section4.A01.AprioriInvariance
import Euler.GainedMildFormula
import Euler.SobolevSmoothProduct

/-! Cross-order compatibility on a prescribed horizon. The sole additional analytic
input is fixed-order, unrestricted mild uniqueness, explicitly named below. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerGainedMildFormula EulerDuhamelDifferentiation EulerSobolevHeatGenerator
open scoped Topology ContDiff NNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
private local instance commonHorizonSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace 1 q) := inferInstance
private local instance commonHorizonSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace 1 q) := inferInstance

/-- Heat evolution commutes with arbitrary Sobolev restriction. -/
theorem restrict_heat {p q : ℕ} (h : q ≤ p) (s : ℝ≥0)
    (u : SobolevSpace 1 p) :
    restrictOperator 1 h (heatOperator 1 p s u) =
      heatOperator 1 q s (restrictOperator 1 h u) := by
  apply value_injective 1
  simp only [value_restrictOperator, heatOperator_value]

-- Elaborating the dependent Sobolev orders and continuous-path coercions.
set_option maxHeartbeats 400000 in
/-- The actual forced quadratic source commutes with restriction. -/
theorem restrict_forced_source {p q : ℕ} (hp : 6 ≤ p) (hq : 6 ≤ q)
    (h : q ≤ p) {S : ℝ} (f : C(Icc (0 : ℝ) S, SobolevSpace 1 p))
    (u : SobolevSpace 1 (p+1)) (t : Icc (0 : ℝ) S) :
    restrictOperator 1 h ((coefficients 1 hp f).apply t u) =
      (coefficients 1 hq ((restrictOperator 1 h).compLeftContinuous ℝ _ f)).apply t
        (restrictOperator 1 (Nat.succ_le_succ h) u) := by
  have hadv : value 1 (advection 1 hp u u) =
      value 1 (advection 1 hq (restrictOperator 1 (Nat.succ_le_succ h) u)
        (restrictOperator 1 (Nat.succ_le_succ h) u)) := by
    unfold advection
    rw [EulerSobolevTransport.transportBilinear_value,
      EulerSobolevTransport.transportBilinear_value]
    apply Finset.sum_congr rfl
    intro i _
    exact EulerSobolevL2Product.scalarProduct_of_value_eq 1 (by omega) (by omega)
      _ _ _ rfl _
  apply value_injective 1
  simp only [value_restrictOperator, source_eq, leray_value]
  apply congrArg (fun z => z - gradientProjection 1 1 0 z)
  change (valueOperator 1 p) (_ - _) = (valueOperator 1 q) (_ - _)
  simp only [map_sub]
  exact congrArg₂ (fun x y => x - y) rfl hadv

/-- Restriction commutes with the ordinary (ungained) heat integral. -/
theorem restrict_duhamel {p q : ℕ} (h : q ≤ p) (ν S : ℝ) (hS : 0 ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 p)) (t : ℝ) :
    restrictOperator 1 h (duhamel 1 ν S hS f t) =
      duhamel 1 ν S hS ((restrictOperator 1 h).compLeftContinuous ℝ _ f) t := by
  unfold duhamel
  rw [← (restrictOperator 1 h).intervalIntegral_comp_comm
    ((shiftedHeat_continuous 1 ν S hS f t).intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact restrict_heat h _ _

-- Elaborating the dependent Sobolev orders and continuous-path coercions.
set_option maxHeartbeats 400000 in
/-- The gained mild path commutes with arbitrary lowering, including its integral. -/
theorem restrict_mildPath {p q : ℕ} (h : q ≤ p) (ν : ℝ) (hν : 0 < ν)
    (S : ℝ) (hS : 0 ≤ S) (a : SobolevSpace 1 (p+1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 p)) (t : Icc (0 : ℝ) S) :
    restrictOperator 1 (Nat.succ_le_succ h) (mildPath 1 p ν hν S hS a f t) =
      mildPath 1 q ν hν S hS (restrictOperator 1 (Nat.succ_le_succ h) a)
        ((restrictOperator 1 h).compLeftContinuous ℝ _ f) t := by
  apply truncate_injective 1 q
  change restrictOperator 1 h (truncateOperator 1 p (mildPath 1 p ν hν S hS a f t)) = _
  rw [mildPath_truncate 1 p, map_add]
  have hd := restrict_duhamel h ν S hS f t.val
  have hh := restrict_heat h (2*ν*t.val).toNNReal (truncateOperator 1 p a)
  exact (congrArg₂ (fun x y => x + y) hh hd).trans
    (mildPath_truncate 1 q ν hν S hS
      (restrictOperator 1 (Nat.succ_le_succ h) a)
      ((restrictOperator 1 h).compLeftContinuous ℝ _ f) t).symm

/-- Bundle the source evaluated along a continuous path. -/
def commonSource {q : ℕ} {S : ℝ}
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1))) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 q) :=
  ⟨fun t => C.apply t (u t), C.continuous.comp (continuous_id.prodMk u.continuous)⟩

/-- On the full horizon the quadratic expression is the gained mild path. -/
theorem quadraticDuhamel_eq_mildPath {q : ℕ} {ν S : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (a : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (t : Icc (0 : ℝ) S) :
    quadraticDuhamel 1 ν hν hS le_rfl C a u t =
      mildPath 1 q ν hν S hS a (commonSource C u) t := by
  rw [mildPath_apply]
  rfl

-- Elaborating the dependent Sobolev orders and continuous-path coercions.
set_option maxHeartbeats 400000 in
/-- The canonical forced Duhamel equation lowers to every order at least six. -/
theorem lower_forced_mild {p q : ℕ} (hp : 6 ≤ p) (hq : 6 ≤ q) (h : q ≤ p)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 ≤ S) (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (p+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 hp (sobolevPath F hF p))
      (ordinarySobolev (p+1) a.toLp a.translation_contDiff) u t) :
    let v := (restrictOperator 1 (Nat.succ_le_succ h)).compLeftContinuous ℝ _ u
    ∀ t, v t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) v t := by
  let C := coefficients 1 hp (sobolevPath F hF p)
  let g := commonSource C u
  have he t : u t = mildPath 1 p ν hν S hS
      (ordinarySobolev (p+1) a.toLp a.translation_contDiff) g t := by
    exact (hu t).trans (quadraticDuhamel_eq_mildPath hν hS C _ u t)
  have hf : (restrictOperator 1 h).compLeftContinuous ℝ _ (sobolevPath F hF p) =
      sobolevPath F hF q := by
    apply ContinuousMap.ext
    intro t
    exact restrict_sobolev h (F t)
  let v := (restrictOperator 1 (Nat.succ_le_succ h)).compLeftContinuous ℝ _ u
  have hg : (restrictOperator 1 h).compLeftContinuous ℝ _ g =
      commonSource (coefficients 1 hq (sobolevPath F hF q)) v := by
    apply ContinuousMap.ext
    intro t
    change restrictOperator 1 h ((coefficients 1 hp (sobolevPath F hF p)).apply t (u t)) = _
    exact (restrict_forced_source hp hq h (sobolevPath F hF p) (u t) t).trans
      (congrArg (fun f => (coefficients 1 hq f).apply t (v t)) hf)
  dsimp only
  intro t
  change restrictOperator 1 (Nat.succ_le_succ h) (u t) = _
  calc
    _ = restrictOperator 1 (Nat.succ_le_succ h)
        (mildPath 1 p ν hν S hS (ordinarySobolev (p+1) a.toLp a.translation_contDiff) g t) :=
      congrArg (restrictOperator 1 (Nat.succ_le_succ h)) (he t)
    _ = mildPath 1 q ν hν S hS
        (restrictOperator 1 (Nat.succ_le_succ h)
          (ordinarySobolev (p+1) a.toLp a.translation_contDiff))
        ((restrictOperator 1 h).compLeftContinuous ℝ _ g) t :=
      restrict_mildPath h ν hν S hS _ g t
    _ = mildPath 1 q ν hν S hS
        (ordinarySobolev (q+1) a.toLp a.translation_contDiff)
        (commonSource (coefficients 1 hq (sobolevPath F hF q)) v) t :=
      congrArg₂ (fun b f => mildPath 1 q ν hν S hS b f t)
        (restrict_sobolev (Nat.succ_le_succ h) a) hg
    _ = _ := (quadraticDuhamel_eq_mildPath hν hS _ _ v t).symm

/-- The remaining analytic input: two order-six mild solutions with identical
initial datum and continuous force agree on the entire prescribed interval.
There is no contraction-ball or small-horizon premise. -/
def MildUniqueness : Prop :=
  ∀ (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S)
    (a : SobolevSpace 1 7) (f : C(Icc (0 : ℝ) S, SobolevSpace 1 6))
    (u v : C(Icc (0 : ℝ) S, SobolevSpace 1 7)),
    (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 le_rfl f) a u t) →
    (∀ t, v t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 le_rfl f) a v t) →
    u = v

/-- One ordinary carrier realizes the canonical solutions at every finite order.
The radii are enlarged internally only to meet the continuation API's initial-norm premise. -/
theorem compatible_carriers_of_boundsInv (huniq : MildUniqueness)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBoundInv hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)),
          ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t := by
  have hex (q : ℕ) (hq : 6 ≤ q) :=
    localTheory_on_prescribed_horizon_of_boundInv hq hν hS
      (R := max (R q) ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖)
      ((norm_nonneg _).trans (le_max_right _ _)) a ha F hF (le_max_right _ _)
      (fun T hT hTS u hu hi => (hb q hq T hT hTS u hu hi).trans (le_max_left _ _))
  obtain ⟨u₆, U, _, _, hU0, hU, _, hu₆, _⟩ := hex 6 le_rfl
  refine ⟨U, hU0, ?_⟩
  intro q hq
  obtain ⟨u, _, _, _, _, _, _, hu, hi⟩ := hex q hq
  let v := (restrictOperator 1 (Nat.succ_le_succ hq)).compLeftContinuous ℝ _ u
  have hv := lower_forced_mild hq (le_refl 6) hq hν hS.le a F hF u hu
  have he : u₆ = v := huniq ν S hν hS _ _ u₆ v hu₆ hv
  refine ⟨u, hfs q hq, ?_, hi, hu⟩
  intro t
  rw [hU, he]
  rfl

/-- The unrestricted a-priori-bound version of the common-carrier theorem. -/
theorem compatible_carriers_of_bounds (huniq : MildUniqueness)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)),
          ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t :=
  compatible_carriers_of_boundsInv huniq hν hS a ha F hF R
    (fun q hq => HasAprioriBound.toInv hq hν a F hF (R q) (hb q hq)) hfs

/-- Lane 178’s existential `hall`, with canonical witnesses supplied by the stronger theorem. -/
theorem compatible_carriers_hall (huniq : MildUniqueness)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ (u₀ : SobolevSpace 1 (q + 1))
          (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
          (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
          ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq f) u₀ u t := by
  obtain ⟨U, hU, hu⟩ := compatible_carriers_of_bounds huniq hν hS a ha F hF R hb hfs
  refine ⟨U, hU, ?_⟩
  intro q hq
  obtain ⟨u, hs, hl, hi, hm⟩ := hu q hq
  exact ⟨ordinarySobolev (q+1) a.toLp a.translation_contDiff,
    sobolevPath F hF q, u, hs, hl, hi, hm⟩

end NSFormalization.Section4.A01
