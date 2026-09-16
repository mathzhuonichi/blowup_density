import NSFormalization.Section4.A01.SmoothTame
import NSFormalization.Section4.A01.SignedPassage

/-! Unconditional cylinder tame estimates and finite mild energy assembly. -/
noncomputable section
namespace NSFormalization.Section4.A01
open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerMildTopWord
  EulerSobolevWordBlocks EulerSobolevL2Product
open Finset
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The transported factor's H³ embedding makes the opposite product integrable. -/
theorem cylinderRightProduct_memLp (L : Vector3 →L[ℝ] ℝ)
    (u : LiftL2 1) (v : SobolevSpace 1 3) :
    MemLp (fun x => L (u x) • value 1 v x) 2 (liftMeasure 1) := by
  apply (Lp.memLp u).of_le_mul
    (c := (‖L‖ * sobolevEmbeddingConstant 1 3) * ‖v‖)
  · exact (L.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).smul
      (Lp.aestronglyMeasurable (value 1 v))
  · filter_upwards [value_ae_bound 1 (by omega : 3 ≤ 3) v] with x hx
    rw [norm_smul]
    exact (mul_le_mul (L.le_opNorm _) hx (norm_nonneg _) (by positivity)).trans_eq
      (by ring)

/-- Actual L² scalar-vector product with the vector factor supplying the embedding. -/
def cylinderRightProduct (L : Vector3 →L[ℝ] ℝ)
    (u : LiftL2 1) (v : SobolevSpace 1 3) : LiftL2 1 :=
  (cylinderRightProduct_memLp L u v).toLp (fun x => L (u x) • value 1 v x)

theorem cylinderRightProduct_ae (L : Vector3 →L[ℝ] ℝ)
    (u : LiftL2 1) (v : SobolevSpace 1 3) :
    (cylinderRightProduct L u v : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
      (fun x => L (u x) • value 1 v x) :=
  (cylinderRightProduct_memLp L u v).coeFn_toLp

theorem cylinderRightProduct_norm (L : Vector3 →L[ℝ] ℝ)
    (u : LiftL2 1) (v : SobolevSpace 1 3) :
    ‖cylinderRightProduct L u v‖ ≤
      (‖L‖ * sobolevEmbeddingConstant 1 3) * ‖v‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [cylinderRightProduct_ae L u v,
    value_ae_bound 1 (by omega : 3 ≤ 3) v] with x hp hv
  rw [hp, norm_smul]
  exact (mul_le_mul (L.le_opNorm _) hv (norm_nonneg _) (by positivity)).trans_eq
    (by ring)

/-- Opposite-orientation mixed estimate, with exactly the same constant as the
coefficient-embedding orientation. Scalar-vector multiplication is not symmetric. -/
theorem cylinderMixedProduct_right {q a b : ℕ} (hq : 6 ≤ q)
    (V : SobolevSpace 1 (2+q)) (ha0 : 1 ≤ a) (hb0 : 1 ≤ b)
    (ha : a ≤ 2+q) (hb : 3+b ≤ 2+q) (hab : a+b ≤ (2+q)+4)
    (w : Fin a → Fin 4) (v : Fin b → Fin 4)
    (L : Vector3 →L[ℝ] ℝ) :
    ‖cylinderRightProduct L (word 1 V ha w) (boundedWordBlock 1 3 b hb v V)‖ ≤
      (‖L‖ * sobolevEmbeddingConstant 1 3) *
        (‖restrictOperator 1 (Nat.succ_le_succ hq)
          (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V) := by
  let W := boundedWordBlock 1 3 b hb v V
  let B := word 1 V ha w
  let R := ‖restrictOperator 1 (Nat.succ_le_succ hq)
    (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hprod : ‖W‖ * ‖B‖ ≤ R := by
    have hs : ‖(‖B‖ : ℝ) • W‖ ≤ R := by
      change ‖((‖B‖ : ℝ) • W).val‖ ≤ R
      apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro z
      change ‖(‖B‖ : ℝ) • (W.val z)‖ ≤ R
      rw [norm_smul, norm_norm, mul_comm]
      have he : W.val z = word 1 V (by have := z.1.isLt; omega : z.1.val+b ≤ 2+q)
          (Fin.append z.2 v) := by
        change word 1 (wordBlock 1 3 b v (restrictOperator 1 hb V))
          (Nat.le_of_lt_succ z.1.isLt) z.2 = _
        rw [wordBlock_word]
        rfl
      rw [he]
      exact (mul_le_mul
        (cylinderWord_norm_le_maximum V (by have := z.1.isLt; omega) (Fin.append z.2 v))
        (cylinderWord_norm_le_maximum V ha w) (norm_nonneg B)
        (cylinderWordMaximum_nonneg V _)).trans
          (cylinderWordMaximum_product_le_gradient hq V (by omega) ha0
            (by have := z.1.isLt; omega) ha (by have := z.1.isLt; omega))
    simpa only [norm_smul, norm_norm, mul_comm] using hs
  exact (cylinderRightProduct_norm L B W).trans
    (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (norm_nonneg L) (sobolevEmbeddingConstant_nonneg 1 3)))

open EulerMetricTransport EulerSobolevWordLevel EulerRealCylinder EulerVectorCylinder EulerTransportDerivatives
open scoped ContDiff

/-- Finite cylinder words agree with every smooth representative, including angular words. -/
theorem cylinderWord_ae {s n : ℕ} (V : SobolevSpace 1 s) (hn : n ≤ s)
    (w : Fin n → Fin 4) (f : LiftDomain 1 → Vector3)
    (hV : (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x)) :
    (word 1 V hn w : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
      iteratedFieldDerivative 1 w f := by
  have h := wordAtLevel_ae 1 0 n w (by omega) V f hV hf
  rw [wordAtLevel_value, toJet_word 1 V hn w] at h
  exact h

/-- Every positive-order Leibniz leaf has an actual L² representative and the
same tame bound, whichever factor has three derivatives of embedding margin. -/
theorem cylinderMixedWord_bound {q a b : ℕ} (hq : 6 ≤ q)
    (V : SobolevSpace 1 (2+q)) (f : LiftDomain 1 → Vector3)
    (hV : (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x))
    (ha0 : 1 ≤ a) (hb0 : 1 ≤ b) (hab : a+b ≤ 2+q)
    (w : Fin a → Fin 4) (v : Fin b → Fin 4) (L : Vector3 →L[ℝ] ℝ) :
    ∃ P : LiftL2 1,
      (P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
        (fun x => L (iteratedFieldDerivative 1 w f x) • iteratedFieldDerivative 1 v f x) ∧
      ‖P‖ ≤ (‖L‖ * sobolevEmbeddingConstant 1 3) *
        (‖restrictOperator 1 (Nat.succ_le_succ hq)
          (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V) := by
  by_cases ha : 3+a ≤ 2+q
  · let W := boundedWordBlock 1 3 a ha w V
    let B := word 1 V (by omega : b ≤ 2+q) v
    refine ⟨scalarProduct 1 (by omega : 3 ≤ 3) L W B, ?_,
      cylinderMixedProduct_left hq V ha0 hb0 ha (by omega) (by omega) w v L⟩
    have hW : (value 1 W : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
        iteratedFieldDerivative 1 w f := by
      rw [show value 1 W = word 1 V (by omega) w from boundedWordBlock_value 1 3 a ha w V]
      exact cylinderWord_ae V (by omega) w f hV hf
    filter_upwards [scalarProduct_ae 1 (by omega : 3 ≤ 3) L W B,
      hW,
      cylinderWord_ae V (by omega : b ≤ 2+q) v f hV hf] with x hp hw hv
    exact hp.trans (by rw [hw, hv])
  · have hb : 3+b ≤ 2+q := by omega
    let W := boundedWordBlock 1 3 b hb v V
    let B := word 1 V (by omega : a ≤ 2+q) w
    refine ⟨cylinderRightProduct L B W, ?_,
      cylinderMixedProduct_right hq V ha0 hb0 (by omega) hb (by omega) w v L⟩
    have hW : (value 1 W : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
        iteratedFieldDerivative 1 v f := by
      rw [show value 1 W = word 1 V (by omega) v from boundedWordBlock_value 1 3 b hb v V]
      exact cylinderWord_ae V (by omega) v f hV hf
    filter_upwards [cylinderRightProduct_ae L B W,
      cylinderWord_ae V (by omega : a ≤ 2+q) w f hV hf,
      hW] with x hp hw hv
    exact hp.trans (by rw [hw, hv])

/-- A quantitative L² bound is preserved by addition of representatives. -/
theorem cylinderL2Bound_add {f g : LiftDomain 1 → Vector3} {A B : ℝ}
    (hf : ∃ P : LiftL2 1, (P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f ∧ ‖P‖ ≤ A)
    (hg : ∃ P : LiftL2 1, (P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] g ∧ ‖P‖ ≤ B) :
    ∃ P : LiftL2 1, (P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f+g ∧ ‖P‖ ≤ A+B := by
  obtain ⟨P, hP, hnP⟩ := hf
  obtain ⟨Q, hQ, hnQ⟩ := hg
  refine ⟨P+Q, ?_, (norm_add_le P Q).trans (add_le_add hnP hnQ)⟩
  filter_upwards [Lp.coeFn_add P Q, hP, hQ] with x hx hp hq
  exact hx.trans (by simp only [Pi.add_apply, hp, hq])

/-- The recursive Leibniz expansion has at most 2^n leaves. This counts
multiplicity without identifying different derivative words. -/
theorem cylinderLeibniz_bound {q : ℕ} (K : ℝ) (f : LiftDomain 1 → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x)) (L : Vector3 →L[ℝ] ℝ)
    (hleaf : ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → a+b ≤ 2+q →
      ∀ (w : Fin a → Fin 4) (v : Fin b → Fin 4),
      ∃ P : LiftL2 1, (P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
        (fun x => L (iteratedFieldDerivative 1 w f x) • iteratedFieldDerivative 1 v f x) ∧
        ‖P‖ ≤ K)
    {n a b : ℕ} (hn : n+a+b ≤ 2+q) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (z : Fin n → Fin 4) (w : Fin a → Fin 4) (v : Fin b → Fin 4) :
    ∃ P : LiftL2 1, (P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
      cylinderLeibniz z (L ∘ iteratedFieldDerivative 1 w f) (iteratedFieldDerivative 1 v f) ∧
      ‖P‖ ≤ (2:ℝ)^n * K := by
  induction n generalizing a b with
  | zero => simpa only [pow_zero, one_mul, cylinderLeibniz, Function.comp_apply] using hleaf a b ha hb (by omega) w v
  | succ n ih =>
    let i := z (Fin.last n)
    have hw : fieldDerivative 1 (standardDirection i) (L ∘ iteratedFieldDerivative 1 w f) =
        L ∘ iteratedFieldDerivative 1 (Fin.cons i w) f := by
      rw [fieldDerivative_postcomp 1 L _ _ (iteratedFieldDerivative_smooth 1 w f hf)]
      rfl
    have hv : fieldDerivative 1 (standardDirection i) (iteratedFieldDerivative 1 v f) =
        iteratedFieldDerivative 1 (Fin.cons i v) f := rfl
    obtain ⟨P, hP, hnorm⟩ := cylinderL2Bound_add
      (ih (by omega) (by omega) hb (Fin.init z) (Fin.cons i w) v)
      (ih (by omega) ha (by omega) (Fin.init z) w (Fin.cons i v))
    refine ⟨P, ?_, ?_⟩
    · rw [cylinderLeibniz]
      change _ =ᵐ[_] cylinderLeibniz _ (fieldDerivative 1 (standardDirection i) _) _ +
        cylinderLeibniz _ _ (fieldDerivative 1 (standardDirection i) _)
      rw [hw, hv]
      exact hP
    · convert hnorm using 1
      rw [pow_succ]
      ring

/-- Counting only surviving commutator branches still costs at most 2^n. -/
theorem cylinderCommutatorLeibniz_bound {q : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (f : LiftDomain 1 → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x)) (L : Vector3 →L[ℝ] ℝ)
    (hleaf : ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → a+b ≤ 2+q →
      ∀ (w : Fin a → Fin 4) (v : Fin b → Fin 4),
      ∃ P : LiftL2 1, (P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
        (fun x => L (iteratedFieldDerivative 1 w f x) • iteratedFieldDerivative 1 v f x) ∧
        ‖P‖ ≤ K)
    {n b : ℕ} (hn : n+b ≤ 2+q) (hb : 1 ≤ b)
    (z : Fin n → Fin 4) (v : Fin b → Fin 4) :
    ∃ P : LiftL2 1, (P : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
      cylinderCommutatorLeibniz z (L ∘ f) (iteratedFieldDerivative 1 v f) ∧
      ‖P‖ ≤ (2:ℝ)^n * K := by
  induction n generalizing b with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · exact Lp.coeFn_zero _ _ _
    · simpa only [norm_zero, pow_zero, one_mul] using hK
  | succ n ih =>
    let i := z (Fin.last n)
    have hw : fieldDerivative 1 (standardDirection i) (L ∘ f) =
        L ∘ iteratedFieldDerivative 1 (fun _ : Fin 1 => i) f := by
      rw [fieldDerivative_postcomp 1 L _ f hf]
      rfl
    have hv : fieldDerivative 1 (standardDirection i) (iteratedFieldDerivative 1 v f) =
        iteratedFieldDerivative 1 (Fin.cons i v) f := rfl
    obtain ⟨P, hP, hnorm⟩ := cylinderL2Bound_add
      (cylinderLeibniz_bound K f hf L hleaf (by omega : n+1+b ≤ 2+q)
        (by omega) hb (Fin.init z) (fun _ : Fin 1 => i) v)
      (ih (by omega) (by omega) (Fin.init z) (Fin.cons i v))
    refine ⟨P, ?_, ?_⟩
    · rw [cylinderCommutatorLeibniz]
      change _ =ᵐ[_] cylinderLeibniz _ (fieldDerivative 1 (standardDirection i) _) _ +
        cylinderCommutatorLeibniz _ _ (fieldDerivative 1 (standardDirection i) _)
      rw [hw, hv]
      exact hP
    · convert hnorm using 1
      rw [pow_succ]
      ring

/-- A derivative operator agrees almost everywhere with the classical derivative. -/
theorem cylinderDerivative_ae {s : ℕ} (V : SobolevSpace 1 (s+1))
    (f : LiftDomain 1 → Vector3)
    (hV : (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x)) (i : Fin 4) :
    (value 1 (derivativeOperator 1 s i V) : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1]
      fieldDerivative 1 (standardDirection i) f :=
  EulerStrongSmoothJet.translation_derivative_ae 1 (standardDirection i)
    (value 1 V) (value 1 (derivativeOperator 1 s i V)) f hV hf
    (derivativeOperator_hasDerivAt 1 i V)

open EulerH6Nonlinear EulerSobolevTransport
-- The two dependent Sobolev operands and their word indices need extra elaboration fuel.
set_option maxHeartbeats 400000 in
/-- Exact a.e. identification of the finite coordinate commutator with the
negative smooth Leibniz expansion. No descent or invariance premise is used. -/
theorem cylinderCoordinateCommutator_ae {q : ℕ} (hq : 6 ≤ q)
    (V : SobolevSpace 1 (2+q)) (f : LiftDomain 1 → Vector3)
    (hV : (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x))
    (i : Fin 4) (w : SobolevWord (q+1)) :
    (cylinderCoordinateCommutator hq
      (restrictOperator 1 (by omega : q+1 ≤ 2+q) V) V i w : LiftDomain 1 → Vector3)
      =ᵐ[liftMeasure 1]
      -cylinderCommutatorLeibniz w.2 (velocityComponents 1 0 i ∘ f)
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

/-- One coordinate word costs at most 2^n embedded mixed products. -/
theorem cylinderCoordinateWord_bound {q : ℕ} (hq : 6 ≤ q)
    (V : SobolevSpace 1 (2+q)) (f : LiftDomain 1 → Vector3)
    (hV : (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x))
    (i : Fin 4) (w : SobolevWord (q+1)) :
    ‖cylinderCoordinateCommutator hq
      (restrictOperator 1 (by omega : q+1 ≤ 2+q) V) V i w‖ ≤
      (2:ℝ)^(q+1) * sobolevEmbeddingConstant 1 3 *
        (‖restrictOperator 1 (Nat.succ_le_succ hq)
          (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V) := by
  let L := velocityComponents 1 0 i
  let R := ‖restrictOperator 1 (Nat.succ_le_succ hq)
    (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V
  let K := (‖L‖ * sobolevEmbeddingConstant 1 3) * R
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (norm_nonneg _) (sobolevEmbeddingConstant_nonneg 1 3)) hR
  obtain ⟨P, hP, hnP⟩ := cylinderCommutatorLeibniz_bound K hK f hf L
    (fun a b ha hb hab w v => cylinderMixedWord_bound hq V f hV hf ha hb hab w v L)
    (by have := w.1.isLt; omega : w.1.val+1 ≤ 2+q) (by omega : 1 ≤ 1)
    w.2 (fun _ : Fin 1 => i)
  have he : cylinderCoordinateCommutator hq
      (restrictOperator 1 (by omega : q+1 ≤ 2+q) V) V i w = -P := by
    apply Lp.ext
    filter_upwards [cylinderCoordinateCommutator_ae hq V f hV hf i w,
      hP, Lp.coeFn_neg P] with x hc hp hn
    rw [hn]
    simp only [Pi.neg_apply]
    rw [hp]
    exact hc
  rw [he, norm_neg]
  have hp : (2:ℝ)^w.1.val ≤ (2:ℝ)^(q+1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ w.1.isLt)
  have hL : ‖L‖ ≤ 1 := velocityComponents_norm 1 0 (by norm_num) (by simp) i
  calc
    ‖P‖ ≤ (2:ℝ)^w.1.val * K := hnP
    _ ≤ (2:ℝ)^(q+1) * K := mul_le_mul_of_nonneg_right hp hK
    _ ≤ (2:ℝ)^(q+1) * (sobolevEmbeddingConstant 1 3 * R) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hL (sobolevEmbeddingConstant_nonneg 1 3))) hR
    _ = _ := by ring

/-- Each word of length at most q+1 has at most 2^(q+1) Leibniz leaves;
summing all Fin 4 words costs their exact cardinality. Each leaf uses the
proved H³ cylinder embedding. The later forcing constant is coordinateTameA,
which also includes lane 196's mildNormConstant through A q. -/
def tameAssemblyConstant (q : ℕ) : ℝ :=
  (Fintype.card (SobolevWord (q+1)) : ℝ) * (2:ℝ)^(q+1) * sobolevEmbeddingConstant 1 3

open EulerFiniteMetricEnergy
/-- Unconditional smooth-cylinder coordinate tame estimate, with an explicit constant. -/
theorem smoothCylinderCoordinateTame {q : ℕ} (hq : 6 ≤ q) :
    SmoothCylinderCoordinateTame q hq (tameAssemblyConstant q) := by
  intro V f hV hf _hfL i
  apply (familyNorm_le_sum_norm _).trans
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (SobolevWord (q+1))))
    (fun w _ => cylinderCoordinateWord_bound hq V f hV hf i w)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    tameAssemblyConstant, mul_assoc] using hsum

/-- The same constant passes to all compatible finite Sobolev elements by density. -/
theorem cylinderCoordinateTame_unconditional {q : ℕ} (hq : 6 ≤ q) :
    CylinderCoordinateTame q hq (tameAssemblyConstant q) :=
  cylinderCoordinateTame hq (smoothCylinderCoordinateTame hq)

/-- Unconditional existence; the older theorem with this stem takes a smooth premise. -/
theorem cylinderCoordinateTame_exists' {q : ℕ} (hq : 6 ≤ q) :
    ∃ C : ℝ, CylinderCoordinateTame q hq C :=
  ⟨tameAssemblyConstant q, cylinderCoordinateTame_unconditional hq⟩

/-- Explicit forcing normalization: includes mildNormConstant via A q and
absorbs the four coordinate sums into the forcing chain's factor sixteen. -/
def tameAssemblyA (q : ℕ) : ℝ := coordinateTameA q (tameAssemblyConstant q)

/-- The finite commutator bound with the certified enlarged constant. -/
theorem cylinderCommutatorBound_unconditional {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q))
    (hV : restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v) :
    familyNorm (cylinderCommutator hq v V) ≤
      tameAssemblyA q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖) *
        cylinderWordGradient V :=
  cylinderCommutatorBound_recut hq (smoothCylinderCoordinateTame hq) v V hV

open Set EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerSmoothFieldSobolevTime EulerQuadraticSource
  EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal

/-- The existing forcing chain accepts the enlarged constant without an analytic input. -/
theorem forcingFamilyBound_unconditional {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ForcingFamilyBound hq hν a F hF (E q) (tameAssemblyA q) :=
  forcingFamilyBound_of_cylinder_recut hq hν a F hF (smoothCylinderCoordinateTame hq)

/-- Unconditional finite mild energy, composing the spatial estimate and signed passage. -/
theorem finiteMildEnergy' {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    FiniteMildEnergy hq hν a ha F hF (E q) (tameAssemblyA q) :=
  finiteMildEnergy_of_forcingBound'' hq hν a ha F hF le_rfl
    (forcingFamilyBound_unconditional hq hν a F hF)

/-- All orders on the base solution's horizon, with no remaining analytic premise. -/
theorem hb_of_base'' {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF
      (aprioriRadius a F hF R₆ E (fun q => tameAssemblyA q^2/(4*ν)) q) :=
  hb_of_base' hν hS a ha F hF u₆ hR h₆ E tameAssemblyA E_nonneg
    (fun _ hq => finiteMildEnergy' hq hν a ha F hF)

end NSFormalization.Section4.A01
