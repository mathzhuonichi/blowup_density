import NSFormalization.Section4.A01.CoordinateTame
import Euler.SobolevInterpolation
import Euler.SobolevWordBlockCoordinates

/-! Finite-order cylinder word interpolation, including the angular direction.
This supplies word interpolation and the coefficient-embedding orientation
of the mixed-product estimate. It does not certify a full commutator constant. -/
noncomputable section
namespace NSFormalization.Section4.A01
open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLiftedWeakDerivative
open Finset
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Maximum at a fixed word length. Outside the available finite order it is zero;
all interpolation statements below explicitly stay within the available order. -/
def cylinderWordMaximum {s : ℕ} (u : SobolevSpace 1 s) (n : ℕ) : ℝ :=
  if h : n ≤ s then
    (univ : Finset (Fin n → Fin 4)).sup' univ_nonempty (fun w => ‖word 1 u h w‖)
  else 0

theorem cylinderWord_norm_le_maximum {s n : ℕ} (u : SobolevSpace 1 s)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    ‖word 1 u hn w‖ ≤ cylinderWordMaximum u n := by
  rw [cylinderWordMaximum, dite_eq_left hn]
  exact le_sup' (fun v => ‖word 1 u hn v‖) (mem_univ w)

theorem cylinderWordMaximum_nonneg {s : ℕ} (u : SobolevSpace 1 s) (n : ℕ) :
    0 ≤ cylinderWordMaximum u n := by
  by_cases hn : n ≤ s
  · exact (norm_nonneg _).trans (cylinderWord_norm_le_maximum u hn (fun _ => 0))
  · simp [cylinderWordMaximum, hn]

/-- Unlike a high-times-high bound, this keeps the actual parent and child norms. -/
theorem cylinderWord_square_le_product {s n : ℕ} (u : SobolevSpace 1 s)
    (h : n+2 ≤ s) (w : Fin n → Fin 4) (i : Fin 4) :
    ‖word 1 u (by omega : n+1 ≤ s) (Fin.cons i w)‖^2 ≤
      ‖word 1 u (by omega : n ≤ s) w‖ *
        ‖word 1 u h (Fin.cons i (Fin.cons i w))‖ := by
  have hp := translation_derivative_pairing 1 (standardDirection i)
    (word 1 u (by omega : n ≤ s) w)
    (word 1 u (by omega : n+1 ≤ s) (Fin.cons i w))
    (word 1 u (by omega : n+1 ≤ s) (Fin.cons i w))
    (word 1 u h (Fin.cons i (Fin.cons i w)))
    (word_hasDerivAt 1 u (by omega : n < s) w i)
    (word_hasDerivAt 1 u (by omega : n+1 < s) (Fin.cons i w) i)
  rw [real_inner_self_eq_norm_sq] at hp
  exact hp.trans_le ((neg_le_abs _).trans (abs_real_inner_le_norm _ _))

/-- Genuine cylinder log-convexity, without discarding the higher word norm. -/
theorem cylinderWordMaximum_logconvex {s : ℕ} (u : SobolevSpace 1 s)
    (n : ℕ) (h : n+2 ≤ s) :
    (cylinderWordMaximum u (n+1))^2 ≤
      cylinderWordMaximum u n * cylinderWordMaximum u (n+2) := by
  have hn : n+1 ≤ s := by omega
  obtain ⟨w, _, hw⟩ := exists_mem_eq_sup' (univ_nonempty :
    (univ : Finset (Fin (n+1) → Fin 4)).Nonempty)
      (fun w => ‖word 1 u hn w‖)
  have he : cylinderWordMaximum u (n+1) = ‖word 1 u hn w‖ := by
    simpa only [cylinderWordMaximum, dite_eq_left hn] using hw
  rw [he]
  have hp := cylinderWord_square_le_product u h (Fin.tail w) (w 0)
  rw [Fin.cons_self_tail] at hp
  exact hp.trans (mul_le_mul
    (cylinderWord_norm_le_maximum u (by omega) (Fin.tail w))
    (cylinderWord_norm_le_maximum u h (Fin.cons (w 0) w))
    (norm_nonneg _) (cylinderWordMaximum_nonneg u n))

/-- Finite-interval cross inequality. No log-convexity beyond order s is assumed. -/
theorem cylinderWordMaximum_cross {s : ℕ} (u : SobolevSpace 1 s)
    (a d : ℕ) (h : a+d+1 ≤ s) :
    cylinderWordMaximum u (a+1) * cylinderWordMaximum u (a+d) ≤
      cylinderWordMaximum u a * cylinderWordMaximum u (a+d+1) := by
  induction d with
  | zero => simp only [Nat.add_zero]; exact le_of_eq (mul_comm _ _)
  | succ d ih =>
    let x := cylinderWordMaximum u
    have hx := cylinderWordMaximum_nonneg u
    have hc := cylinderWordMaximum_logconvex u (a+d) (by omega)
    have hi := ih (by omega)
    change x (a+1) * x (a+d.succ) ≤ x a * x (a+d.succ+1)
    by_cases hz : x (a+d) = 0
    · have hz' : x (a+d+1) = 0 := by
        change (x (a+d+1))^2 ≤ x (a+d)*x (a+d+2) at hc
        rw [hz, zero_mul] at hc
        nlinarith [hx (a+d+1)]
      simpa only [Nat.add_succ, hz', mul_zero] using mul_nonneg (hx a) (hx (a+d+2))
    · have hp : 0 < x (a+d) := lt_of_le_of_ne (hx _) (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hp).mp
      calc
        x (a+d)*(x (a+1)*x (a+d.succ)) =
            (x (a+1)*x (a+d))*x (a+d+1) := by simp only [Nat.add_succ]; ring
        _ ≤ (x a*x (a+d+1))*x (a+d+1) := mul_le_mul_of_nonneg_right hi (hx _)
        _ = x a*(x (a+d+1))^2 := by ring
        _ ≤ x a*(x (a+d)*x (a+d+2)) := mul_le_mul_of_nonneg_left hc (hx a)
        _ = x (a+d)*(x a*x (a+d.succ+1)) := by simp only [Nat.add_succ]; ring

/-- Move a pair of intermediate orders to the ends, with constant one. -/
theorem cylinderWordMaximum_pair {s : ℕ} (u : SobolevSpace 1 s)
    (a k d : ℕ) (h : a+2*k+d ≤ s) :
    cylinderWordMaximum u (a+k) * cylinderWordMaximum u (a+k+d) ≤
      cylinderWordMaximum u a * cylinderWordMaximum u (a+2*k+d) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    have hc := cylinderWordMaximum_cross u (a+k) (d+1) (by omega)
    have hh := ih (d+2) (by omega)
    convert hc.trans hh using 1 <;> congr 2 <;> omega

/-- Endpoint product interpolation on the actual four-direction cylinder words. -/
theorem cylinderWordMaximum_between {s : ℕ} (u : SobolevSpace 1 s)
    (l a b : ℕ) (hla : l ≤ a) (hab : a ≤ b) (hs : a+b-l ≤ s) :
    cylinderWordMaximum u a * cylinderWordMaximum u b ≤
      cylinderWordMaximum u l * cylinderWordMaximum u (a+b-l) := by
  have h := cylinderWordMaximum_pair u l (a-l) (b-a) (by omega)
  convert h using 1 <;> congr 2 <;> omega

/-- Bound an available maximum by the low restriction, without a cardinality loss. -/
theorem cylinderWordMaximum_le_restrict {s l n : ℕ} (u : SobolevSpace 1 s)
    (hl : l ≤ s) (hn : n ≤ l) :
    cylinderWordMaximum u n ≤ ‖restrictOperator 1 hl u‖ := by
  rw [cylinderWordMaximum, dite_eq_left (hn.trans hl)]
  apply sup'_le
  intro w _
  exact word_norm_le 1 (restrictOperator 1 hl u) ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩

/-- Cylinder analogue of the vendor word-maximum product bound, at any low order l.
The high norm is a finite Sobolev norm, not yet the gradient norm of the target. -/
theorem cylinderWordMaximum_product_le {s l a b : ℕ} (u : SobolevSpace 1 s)
    (hl : l ≤ s) (ha : a ≤ s) (hb : b ≤ s) (hab : a+b ≤ s+l) :
    cylinderWordMaximum u a * cylinderWordMaximum u b ≤
      ‖restrictOperator 1 hl u‖ * ‖u‖ := by
  have high (n : ℕ) (hn : n ≤ s) : cylinderWordMaximum u n ≤ ‖u‖ := by
    simpa only [restrictOperator_self] using cylinderWordMaximum_le_restrict u (le_refl s) hn
  by_cases hal : a ≤ l
  · exact mul_le_mul (cylinderWordMaximum_le_restrict u hl hal) (high b hb)
      (cylinderWordMaximum_nonneg u b) (norm_nonneg _)
  by_cases hbl : b ≤ l
  · rw [mul_comm (cylinderWordMaximum u a)]
    exact mul_le_mul (cylinderWordMaximum_le_restrict u hl hbl) (high a ha)
      (cylinderWordMaximum_nonneg u a) (norm_nonneg _)
  have he (c d : ℕ) (hlc : l ≤ c) (hcd : c ≤ d) (hs : c+d-l ≤ s) :
      cylinderWordMaximum u c * cylinderWordMaximum u d ≤
        ‖restrictOperator 1 hl u‖ * ‖u‖ :=
    (cylinderWordMaximum_between u l c d hlc hcd hs).trans
      (mul_le_mul (cylinderWordMaximum_le_restrict u hl (le_refl l)) (high _ hs)
        (cylinderWordMaximum_nonneg u _) (norm_nonneg _))
  rcases le_total a b with h | h
  · exact he a b (by omega) h (by omega)
  · rw [mul_comm (cylinderWordMaximum u a)]
    exact he b a (by omega) h (by omega)

-- Dependent word indices and the nested gradient sum require additional elaboration fuel.
set_option maxHeartbeats 400000 in
/-- Every positive-order word is an entry of the precise gradient array used
by the forcing chain. This has constant one and no angular-invariance premise. -/
theorem cylinderWordMaximum_le_gradient {q n : ℕ} (V : SobolevSpace 1 (2+q))
    (hn : 1 ≤ n) (hs : n ≤ 2+q) :
    cylinderWordMaximum V n ≤ cylinderWordGradient V := by
  rw [cylinderWordMaximum, dite_eq_left hs]
  apply sup'_le
  intro w _
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let v : SobolevWord (q+1) := ⟨⟨k, by omega⟩, Fin.init w⟩
  let i := w (Fin.last k)
  have he : word 1 V hs w =
      (derivativeOperator 1 (q+1) i
        (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val v := by
    change V.val ⟨⟨k+1, _⟩, w⟩ = V.val ⟨⟨k+1, _⟩, Fin.snoc (Fin.init w) (w (Fin.last k))⟩
    rw [Fin.snoc_init_self]
  rw [he]
  unfold cylinderWordGradient
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  let f (j : Fin 4) (w : SobolevWord (q+1)) : ℝ :=
    ‖(derivativeOperator 1 (q+1) j
      (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w‖^2
  have hf (j : Fin 4) (w : SobolevWord (q+1)) : 0 ≤ f j w := sq_nonneg _
  have hinner : f i v ≤ ∑ w : SobolevWord (q+1), f i w :=
    single_le_sum (fun w _ => hf i w) (mem_univ v)
  have houter : (∑ w : SobolevWord (q+1), f i w) ≤ ∑ j : Fin 4, ∑ w, f j w :=
    single_le_sum (fun j _ => sum_nonneg (fun w _ => hf j w)) (mem_univ i)
  exact hinner.trans houter

/-- The interpolation product already has the exact low-times-gradient shape.
Both orders must be positive; the missing step is an L² bound for their
pointwise mixed product, not for this product of L² norms. -/
theorem cylinderWordMaximum_product_le_gradient {q a b : ℕ} (hq : 6 ≤ q)
    (V : SobolevSpace 1 (2+q)) (ha0 : 1 ≤ a) (hb0 : 1 ≤ b)
    (ha : a ≤ 2+q) (hb : b ≤ 2+q) (hab : a+b ≤ (2+q)+7) :
    cylinderWordMaximum V a * cylinderWordMaximum V b ≤
      ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V := by
  rw [restrictOperator_comp]
  have hl : 7 ≤ 2+q := by omega
  by_cases hal : a ≤ 7
  · exact mul_le_mul (cylinderWordMaximum_le_restrict V hl hal)
      (cylinderWordMaximum_le_gradient V hb0 hb)
      (cylinderWordMaximum_nonneg V b) (norm_nonneg _)
  by_cases hbl : b ≤ 7
  · rw [mul_comm (cylinderWordMaximum V a)]
    exact mul_le_mul (cylinderWordMaximum_le_restrict V hl hbl)
      (cylinderWordMaximum_le_gradient V ha0 ha)
      (cylinderWordMaximum_nonneg V a) (norm_nonneg _)
  have he (c d : ℕ) (hc : 7 < c) (hcd : c ≤ d) (hs : c+d-7 ≤ 2+q) :
      cylinderWordMaximum V c * cylinderWordMaximum V d ≤
        ‖restrictOperator 1 hl V‖ * cylinderWordGradient V :=
    (cylinderWordMaximum_between V 7 c d (by omega) hcd hs).trans
      (mul_le_mul (cylinderWordMaximum_le_restrict V hl (le_refl 7))
        (cylinderWordMaximum_le_gradient V (by omega) hs)
        (cylinderWordMaximum_nonneg V _) (norm_nonneg _))
  rcases le_total a b with h | h
  · exact he a b (by omega) h (by omega)
  · rw [mul_comm (cylinderWordMaximum V a)]
    exact he b a (by omega) h (by omega)

open EulerMildTopWord EulerSobolevWordBlocks EulerSobolevL2Product

/-- A genuine mixed scalar-vector product estimate when the coefficient word
has three derivatives of embedding margin. The constant is the proved cylinder
H³ embedding constant times the coordinate functional norm. -/
theorem cylinderMixedProduct_left {q a b : ℕ} (hq : 6 ≤ q)
    (V : SobolevSpace 1 (2+q)) (ha0 : 1 ≤ a) (hb0 : 1 ≤ b)
    (ha : 3+a ≤ 2+q) (hb : b ≤ 2+q) (hab : a+b ≤ (2+q)+4)
    (w : Fin a → Fin 4) (v : Fin b → Fin 4)
    (L : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ) :
    ‖scalarProduct 1 (by omega : 3 ≤ 3) L (boundedWordBlock 1 3 a ha w V)
        (word 1 V hb v)‖ ≤
      (‖L‖ * sobolevEmbeddingConstant 1 3) *
        (‖restrictOperator 1 (Nat.succ_le_succ hq)
          (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V) := by
  let W := boundedWordBlock 1 3 a ha w V
  let B := word 1 V hb v
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
      have he : W.val z = word 1 V (by have := z.1.isLt; omega : z.1.val+a ≤ 2+q)
          (Fin.append z.2 w) := by
        change word 1 (wordBlock 1 3 a w (restrictOperator 1 ha V))
          (Nat.le_of_lt_succ z.1.isLt) z.2 = _
        rw [wordBlock_word]
        rfl
      rw [he]
      exact (mul_le_mul
        (cylinderWord_norm_le_maximum V (by have := z.1.isLt; omega) (Fin.append z.2 w))
        (cylinderWord_norm_le_maximum V hb v) (norm_nonneg B)
        (cylinderWordMaximum_nonneg V _)).trans
          (cylinderWordMaximum_product_le_gradient hq V (by omega) hb0
            (by have := z.1.isLt; omega) hb (by have := z.1.isLt; omega))
    simpa only [norm_smul, norm_norm, mul_comm] using hs
  exact (scalarProduct_norm 1 (by omega : 3 ≤ 3) L W B).trans
    (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (norm_nonneg L) (sobolevEmbeddingConstant_nonneg 1 3)))

end NSFormalization.Section4.A01
