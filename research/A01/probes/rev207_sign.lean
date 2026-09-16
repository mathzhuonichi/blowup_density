import NSFormalization.Section4.A01.TameAssembly
noncomputable section
namespace NSFormalization.Section4.A01
open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerMildTopWord
  EulerSobolevWordBlocks EulerSobolevL2Product
open Finset
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

open EulerMetricTransport EulerSobolevWordLevel EulerRealCylinder EulerVectorCylinder EulerTransportDerivatives EulerH6Nonlinear EulerSobolevTransport EulerFiniteMetricEnergy
open scoped ContDiff
-- The two dependent Sobolev operands and their word indices need extra elaboration fuel.
set_option maxHeartbeats 400000 in
/-- Exact a.e. identification of the finite coordinate commutator with the
negative smooth Leibniz expansion. No descent or invariance premise is used. -/
theorem rev207_positiveCommutator_ae {q : ℕ} (hq : 6 ≤ q)
    (V : SobolevSpace 1 (2+q)) (f : LiftDomain 1 → Vector3)
    (hV : (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x))
    (i : Fin 4) (w : SobolevWord (q+1)) :
    (cylinderCoordinateCommutator hq
      (restrictOperator 1 (by omega : q+1 ≤ 2+q) V) V i w : LiftDomain 1 → Vector3)
      =ᵐ[liftMeasure 1]
      cylinderCommutatorLeibniz w.2 (velocityComponents 1 0 i ∘ f)
        (fieldDerivative 1 (standardDirection i) f) := by
  let L := velocityComponents 1 0 i
  let u := restrictOperator 1 (by omega : q+1 ≤ 2+q) V
  let D := derivativeOperator 1 (q+1) i
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)
  let W := boundedWordBlock 1 1 w.1.val (by have := w.1.isLt; omega) w.2 V
  let T := value 1 (derivativeOperator 1 0 i W)
  let P := productHq 1 (by omega : 6 ≤ q+1) L
    (velocityComponents_norm 1 0 (by norm_num) (by simp) i) u D
  have hu : (value 1 u : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f := hV
  have hD : (value 1 D : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
      fieldDerivative 1 (standardDirection i) f :=
    cylinderDerivative_ae _ f hV hf i
  have hW : (value 1 W : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
      iteratedFieldDerivative 1 w.2 f := by
    rw [show value 1 W = word 1 V (by have := w.1.isLt; omega) w.2 from
      boundedWordBlock_value 1 1 w.1.val _ w.2 V]
    exact cylinderWord_ae V _ w.2 f hV hf
  have hT := cylinderDerivative_ae W _ hW (iteratedFieldDerivative_smooth 1 w.2 f hf) i
  have hP : (value 1 P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
      (fun x => L (f x) • fieldDerivative 1 (standardDirection i) f x) := by
    filter_upwards [productHq_ae 1 (by omega : 6 ≤ q+1) L
      (velocityComponents_norm 1 0 (by norm_num) (by simp) i) u D, hu, hD] with x hp hx hd
    exact hp.trans (by rw [hx, hd])
  have hPs : ∀ x, ContDiff ℝ ∞ (localFieldLift 1
      (fun x => L (f x) • fieldDerivative 1 (standardDirection i) f x) x) := by
    intro x
    exact (postcomp_smooth 1 L f hf x).smul (fieldDerivative_smooth 1 _ f hf x)
  have hwP := cylinderWord_ae P (Nat.le_of_lt_succ w.1.isLt) w.2 _ hP hPs
  have hs := cylinderCoordinateLeibniz_sign w.2 i (L ∘ f) f
    (postcomp_smooth 1 L f hf) hf
  change ((scalarProduct 1 (by omega : 3 ≤ q+1) L u T -
    word 1 P (Nat.le_of_lt_succ w.1.isLt) w.2 : LiftL2 1) : LiftDomain 1 → Vector3)
    =ᵐ[liftMeasure 1] _
  filter_upwards [Lp.coeFn_sub (scalarProduct 1 (by omega : 3 ≤ q+1) L u T)
      (word 1 P (Nat.le_of_lt_succ w.1.isLt) w.2),
    scalarProduct_ae 1 (by omega : 3 ≤ q+1) L u T, hu, hT, hwP] with x hx hp hu ht hw
  simp only [Pi.sub_apply] at hx
  rw [hx, hp, hu, ht, hw]
  exact congrFun hs x


end NSFormalization.Section4.A01
