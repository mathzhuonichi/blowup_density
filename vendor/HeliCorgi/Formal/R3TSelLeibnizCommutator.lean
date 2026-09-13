import Formal.R3TSelSchwartzCalculus
import Formal.R3TSelBridge

/-!
# SEL-4 discharged: the BKM derivative-tuple commutator estimate

This file proves the open T-SEL bridge statement `R3TSelKatoPonceCommutator`
(`Formal/R3TSelBridge.lean`): there is a constant `C ≥ 0` such that for every direction
tuple `v` of length `n ≤ 3` and every Schwartz velocity `φ`,

`‖∂^v((φ·∇)φ) − (φ·∇)(∂^v φ)‖_{L²} ≤ C ‖∇φ‖_{L∞} ‖J³φ‖_{L²}`.

Route (all on the Schwartz core):

1. the convection is the sum over `i` of the scalar–vector products
   `φᵢ • ∂ᵢφ` (`r3SchwartzConvection_eq_sum_smul`), and line derivatives commute
   (`lineDerivOp_comm`), so the commutator splits into the per-`i` Leibniz commutators
   of `∂^v(a • w) − a • ∂^v w`;
2. the exact Leibniz expansions for `n = 1, 2, 3`
   (`smul_commutator_one/two/three`) exhibit the commutator as a sum of products
   `(∂-tuple of a) • (∂-tuple of w)` in which **every scalar factor carries at least one
   derivative** and the total order is `n + 1 ≤ 4`;
3. each product is bounded in `L²` by one of three modes: sup on the first-order factor
   (`≤ ‖∇φ‖_{L∞}` by `norm_lineDerivOp_coordinate_le_gradSup` /
   `norm_lineDerivOp_stdBasis_le_gradSup`) times the `L²` norm of the complementary
   tuple (`≤ (2π)³‖J³φ‖` by `norm_toLp_tuple_le`), or — for the balanced second-order ×
   second-order products — Cauchy–Schwarz into two quartic integrals, each controlled by
   the by-parts Gagliardo–Nirenberg interpolation `r3TSel_gn_quartic` with the sup again
   landing on a first-order factor.

The proved constant is explicit but not optimized; only `∃ C ≥ 0` is consumed
downstream.  The divergence-free hypothesis of the paper statement is not needed for the
commutator and does not appear.
-/

namespace MNS2

open MeasureTheory SchwartzMap LineDeriv Real
open scoped FourierTransform SchwartzMap ENNReal NNReal ContDiff

noncomputable section

/-! ## Exact Leibniz commutator expansions -/

theorem smul_commutator_one (m₁ : R3) (a : R3SchwartzScalar) (w : R3SchwartzVelocity) :
    ∂_{m₁} (r3SchwartzSMul a w) - r3SchwartzSMul a (∂_{m₁} w) =
      r3SchwartzSMul (∂_{m₁} a) w := by
  rw [lineDerivOp_r3SchwartzSMul]
  abel

theorem smul_commutator_two (m₁ m₂ : R3) (a : R3SchwartzScalar)
    (w : R3SchwartzVelocity) :
    ∂_{m₁} (∂_{m₂} (r3SchwartzSMul a w)) -
        r3SchwartzSMul a (∂_{m₁} (∂_{m₂} w)) =
      r3SchwartzSMul (∂_{m₁} (∂_{m₂} a)) w +
        r3SchwartzSMul (∂_{m₂} a) (∂_{m₁} w) +
        r3SchwartzSMul (∂_{m₁} a) (∂_{m₂} w) := by
  simp only [lineDerivOp_r3SchwartzSMul, lineDerivOp_add]
  abel

theorem smul_commutator_three (m₁ m₂ m₃ : R3) (a : R3SchwartzScalar)
    (w : R3SchwartzVelocity) :
    ∂_{m₁} (∂_{m₂} (∂_{m₃} (r3SchwartzSMul a w))) -
        r3SchwartzSMul a (∂_{m₁} (∂_{m₂} (∂_{m₃} w))) =
      r3SchwartzSMul (∂_{m₁} (∂_{m₂} (∂_{m₃} a))) w +
        (r3SchwartzSMul (∂_{m₂} (∂_{m₃} a)) (∂_{m₁} w) +
          r3SchwartzSMul (∂_{m₁} (∂_{m₃} a)) (∂_{m₂} w) +
          r3SchwartzSMul (∂_{m₁} (∂_{m₂} a)) (∂_{m₃} w)) +
        (r3SchwartzSMul (∂_{m₃} a) (∂_{m₁} (∂_{m₂} w)) +
          r3SchwartzSMul (∂_{m₂} a) (∂_{m₁} (∂_{m₃} w)) +
          r3SchwartzSMul (∂_{m₁} a) (∂_{m₂} (∂_{m₃} w))) := by
  simp only [lineDerivOp_r3SchwartzSMul, lineDerivOp_add]
  abel

/-! ## Integrability of Schwartz powers -/

theorem integrable_sq_velocity (ψ : R3SchwartzVelocity) :
    Integrable (fun x : R3 => ‖ψ x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq
    (ψ.continuous.aestronglyMeasurable.norm)).mp ((ψ.memLp 2).norm)

theorem integrable_sq_scalar (b : R3SchwartzScalar) :
    Integrable (fun x : R3 => ‖b x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq
    (b.continuous.aestronglyMeasurable.norm)).mp ((b.memLp 2).norm)

theorem integrable_sq_mul (b : R3SchwartzScalar) (y : R3SchwartzVelocity) :
    Integrable (fun x : R3 => ‖b x‖ ^ 2 * ‖y x‖ ^ 2) volume := by
  refine (integrable_sq_velocity (r3SchwartzSMul b y)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show ‖(r3SchwartzSMul b y) x‖ ^ 2 = ‖b x‖ ^ 2 * ‖y x‖ ^ 2
  rw [r3SchwartzSMul_apply, norm_smul, mul_pow]

theorem integrable_pow4_scalar (b : R3SchwartzScalar) :
    Integrable (fun x : R3 => ‖b x‖ ^ 4) volume := by
  obtain ⟨B, hB0, hB⟩ := exists_sup_bound (F := ℂ) b
  refine ((b.integrable).norm.const_mul (B ^ 3)).mono'
    (b.continuous.norm.pow 4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := hB x
  have h2 : (0 : ℝ) ≤ ‖b x‖ := norm_nonneg _
  have h3 : ‖b x‖ ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ h2 h1 3
  calc ‖b x‖ ^ 4 = ‖b x‖ ^ 3 * ‖b x‖ := by ring
    _ ≤ B ^ 3 * ‖b x‖ := mul_le_mul_of_nonneg_right h3 h2

theorem integrable_pow4_velocity (y : R3SchwartzVelocity) :
    Integrable (fun x : R3 => ‖y x‖ ^ 4) volume := by
  obtain ⟨B, hB0, hB⟩ := exists_sup_bound (F := R3C) y
  refine ((y.integrable).norm.const_mul (B ^ 3)).mono'
    (y.continuous.norm.pow 4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := hB x
  have h2 : (0 : ℝ) ≤ ‖y x‖ := norm_nonneg _
  have h3 : ‖y x‖ ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ h2 h1 3
  calc ‖y x‖ ^ 4 = ‖y x‖ ^ 3 * ‖y x‖ := by ring
    _ ≤ B ^ 3 * ‖y x‖ := mul_le_mul_of_nonneg_right h3 h2

/-! ## The three product-bound modes -/

/-- The scalar `L²` norm of a Schwartz scalar as an integral. -/
theorem sq_norm_toLp_two_scalar (b : R3SchwartzScalar) :
    ‖(b.toLp 2 : Lp ℂ 2 (volume : Measure R3))‖ ^ 2 = ∫ x : R3, ‖b x‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp]
  exact sq_toReal_eLpNorm_two (b.memLp 2)

/-- The squared `L²` norm of a scalar–vector product as an integral. -/
theorem sq_norm_toLp_smul (b : R3SchwartzScalar) (y : R3SchwartzVelocity) :
    ‖((r3SchwartzSMul b y).toLp 2 : R3L2Velocity)‖ ^ 2 =
      ∫ x : R3, ‖b x‖ ^ 2 * ‖y x‖ ^ 2 := by
  rw [sq_norm_toLp_two]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ‖(r3SchwartzSMul b y) x‖ ^ 2 = ‖b x‖ ^ 2 * ‖y x‖ ^ 2
  rw [r3SchwartzSMul_apply, norm_smul, mul_pow]

/-- Mode 1: sup on the scalar factor. -/
theorem norm_toLp_smul_le_sup_left (b : R3SchwartzScalar) (y : R3SchwartzVelocity)
    {B K : ℝ} (hB : ∀ x : R3, ‖b x‖ ≤ B) (hK0 : 0 ≤ K)
    (hy : ‖(y.toLp 2 : R3L2Velocity)‖ ≤ K) :
    ‖((r3SchwartzSMul b y).toLp 2 : R3L2Velocity)‖ ≤ B * K := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsq : ‖((r3SchwartzSMul b y).toLp 2 : R3L2Velocity)‖ ^ 2 ≤ B ^ 2 * K ^ 2 := by
    rw [sq_norm_toLp_smul]
    have h1 : (∫ x : R3, ‖b x‖ ^ 2 * ‖y x‖ ^ 2) ≤
        ∫ x : R3, B ^ 2 * ‖y x‖ ^ 2 := by
      refine integral_mono (integrable_sq_mul b y)
        ((integrable_sq_velocity y).const_mul _) fun x => ?_
      have h2 := hB x
      have h3 : (0 : ℝ) ≤ ‖b x‖ := norm_nonneg _
      have h4 : ‖b x‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ h3 h2 2
      exact mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
    refine h1.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h5 : (∫ x : R3, ‖y x‖ ^ 2) = ‖(y.toLp 2 : R3L2Velocity)‖ ^ 2 :=
      (sq_norm_toLp_two y).symm
    rw [h5]
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  nlinarith [norm_nonneg ((r3SchwartzSMul b y).toLp 2 : R3L2Velocity),
    mul_nonneg hB0 hK0]

/-- Mode 2: sup on the vector factor. -/
theorem norm_toLp_smul_le_sup_right (b : R3SchwartzScalar) (y : R3SchwartzVelocity)
    {B K : ℝ} (hB : ∀ x : R3, ‖y x‖ ≤ B) (hK0 : 0 ≤ K)
    (hb : ‖(b.toLp 2 : Lp ℂ 2 (volume : Measure R3))‖ ≤ K) :
    ‖((r3SchwartzSMul b y).toLp 2 : R3L2Velocity)‖ ≤ B * K := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsq : ‖((r3SchwartzSMul b y).toLp 2 : R3L2Velocity)‖ ^ 2 ≤ B ^ 2 * K ^ 2 := by
    rw [sq_norm_toLp_smul]
    have h1 : (∫ x : R3, ‖b x‖ ^ 2 * ‖y x‖ ^ 2) ≤
        ∫ x : R3, B ^ 2 * ‖b x‖ ^ 2 := by
      refine integral_mono (integrable_sq_mul b y)
        ((integrable_sq_scalar b).const_mul _) fun x => ?_
      have h2 := hB x
      have h3 : (0 : ℝ) ≤ ‖y x‖ := norm_nonneg _
      have h4 : ‖y x‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ h3 h2 2
      calc ‖b x‖ ^ 2 * ‖y x‖ ^ 2 ≤ ‖b x‖ ^ 2 * B ^ 2 :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
        _ = B ^ 2 * ‖b x‖ ^ 2 := by ring
    refine h1.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h5 : (∫ x : R3, ‖b x‖ ^ 2) =
        ‖(b.toLp 2 : Lp ℂ 2 (volume : Measure R3))‖ ^ 2 :=
      (sq_norm_toLp_two_scalar b).symm
    rw [h5]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  nlinarith [norm_nonneg ((r3SchwartzSMul b y).toLp 2 : R3L2Velocity),
    mul_nonneg hB0 hK0]

/-- Mode 3: Cauchy–Schwarz into two quartic integrals. -/
theorem sq_norm_toLp_smul_le_of_quartics (b : R3SchwartzScalar)
    (y : R3SchwartzVelocity) {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hb : (∫ x : R3, ‖b x‖ ^ 4) ≤ Q) (hy : (∫ x : R3, ‖y x‖ ^ 4) ≤ Q) :
    ‖((r3SchwartzSMul b y).toLp 2 : R3L2Velocity)‖ ^ 2 ≤ Q := by
  rw [sq_norm_toLp_smul]
  have hcs := integral_mul_le_sqrt_mul_sqrt
    (f := fun x : R3 => ‖b x‖ ^ 2) (g := fun x : R3 => ‖y x‖ ^ 2)
    (fun x => sq_nonneg _) (fun x => sq_nonneg _)
    (b.continuous.norm.pow 2).aestronglyMeasurable
    (y.continuous.norm.pow 2).aestronglyMeasurable
    ((integrable_pow4_scalar b).congr
      (Filter.Eventually.of_forall fun x => by ring_nf))
    ((integrable_pow4_velocity y).congr
      (Filter.Eventually.of_forall fun x => by ring_nf))
  refine hcs.trans ?_
  have hb4 : (∫ x : R3, (‖b x‖ ^ 2) ^ 2) = ∫ x : R3, ‖b x‖ ^ 4 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hy4 : (∫ x : R3, (‖y x‖ ^ 2) ^ 2) = ∫ x : R3, ‖y x‖ ^ 4 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hb4, hy4]
  calc Real.sqrt (∫ x : R3, ‖b x‖ ^ 4) * Real.sqrt (∫ x : R3, ‖y x‖ ^ 4)
      ≤ Real.sqrt Q * Real.sqrt Q :=
        mul_le_mul (Real.sqrt_le_sqrt hb) (Real.sqrt_le_sqrt hy)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Q := Real.mul_self_sqrt hQ0


/-! ## Object bounds: sups, `L²` norms, and quartics of the derived factors -/

/-- The coordinate derivative is the standard-basis line derivative. -/
theorem r3SchwartzCoordinateDerivative_eq (i : Fin 3) (ψ : R3SchwartzVelocity) :
    r3SchwartzCoordinateDerivative i ψ = ∂_{r3StdBasis i} ψ := by
  rw [show r3SchwartzCoordinateDerivative i ψ = ∂_{r3CoordinateDirection i} ψ from rfl,
    r3CoordinateDirection_eq_stdBasis]

/-- `toLp` is additive on Schwartz velocities. -/
theorem r3Schwartz_toLp_add (X Y : R3SchwartzVelocity) :
    ((X + Y).toLp 2 : R3L2Velocity) =
      (X.toLp 2 : R3L2Velocity) + (Y.toLp 2 : R3L2Velocity) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [(X + Y).coeFn_toLp 2 (volume : Measure R3),
    X.coeFn_toLp 2 (volume : Measure R3), Y.coeFn_toLp 2 (volume : Measure R3),
    MeasureTheory.Lp.coeFn_add (X.toLp 2 : R3L2Velocity) (Y.toLp 2 : R3L2Velocity)]
    with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]
  rfl

/-- `toLp` respects subtraction on Schwartz velocities. -/
theorem r3Schwartz_toLp_sub (X Y : R3SchwartzVelocity) :
    ((X - Y).toLp 2 : R3L2Velocity) =
      (X.toLp 2 : R3L2Velocity) - (Y.toLp 2 : R3L2Velocity) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [(X - Y).coeFn_toLp 2 (volume : Measure R3),
    X.coeFn_toLp 2 (volume : Measure R3), Y.coeFn_toLp 2 (volume : Measure R3),
    MeasureTheory.Lp.coeFn_sub (X.toLp 2 : R3L2Velocity) (Y.toLp 2 : R3L2Velocity)]
    with x h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3]
  rfl

/-- The scalar coordinate has smaller `L²` norm than the field. -/
theorem norm_toLp_coordinate_le (j : Fin 3) (ψ : R3SchwartzVelocity) :
    ‖((r3SchwartzCoordinate j ψ).toLp 2 : Lp ℂ 2 (volume : Measure R3))‖ ≤
      ‖(ψ.toLp 2 : R3L2Velocity)‖ := by
  have hsq : ‖((r3SchwartzCoordinate j ψ).toLp 2 : Lp ℂ 2 (volume : Measure R3))‖ ^ 2 ≤
      ‖(ψ.toLp 2 : R3L2Velocity)‖ ^ 2 := by
    rw [sq_norm_toLp_two_scalar, sq_norm_toLp_two]
    refine integral_mono (integrable_sq_scalar _) (integrable_sq_velocity _) fun x => ?_
    have h1 : ‖(r3SchwartzCoordinate j ψ) x‖ ≤ ‖ψ x‖ := by
      rw [show (r3SchwartzCoordinate j ψ) x = ψ x j from rfl]
      exact norm_coord_le_norm_r3C _ j
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [norm_nonneg ((r3SchwartzCoordinate j ψ).toLp 2 :
      Lp ℂ 2 (volume : Measure R3)),
    norm_nonneg (ψ.toLp 2 : R3L2Velocity)]

/-- Nested-derivative `L²` bounds by the carrier norm: order one. -/
theorem norm_toLp_d1_le (c1 : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} φ).toLp 2 : R3L2Velocity)‖ ≤
      (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ :=
  norm_toLp_tuple_le (n := 1) (by norm_num) ![c1] φ

/-- Nested-derivative `L²` bounds by the carrier norm: order two. -/
theorem norm_toLp_d2_le (c1 c2 : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)).toLp 2 : R3L2Velocity)‖ ≤
      (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ :=
  norm_toLp_tuple_le (n := 2) (by norm_num) ![c1, c2] φ

/-- Nested-derivative `L²` bounds by the carrier norm: order three. -/
theorem norm_toLp_d3_le (c1 c2 c3 : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (∂_{r3StdBasis c3} φ))).toLp 2 :
        R3L2Velocity)‖ ≤
      (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ :=
  norm_toLp_tuple_le (n := 3) (by norm_num) ![c1, c2, c3] φ

/-- Scalar nested-derivative `L²` bounds: order one. -/
theorem norm_toLp_scalar_d1_le (c1 j : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} (r3SchwartzCoordinate j φ)).toLp 2 :
        Lp ℂ 2 (volume : Measure R3))‖ ≤
      (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by
  rw [lineDerivOp_r3SchwartzCoordinate]
  exact (norm_toLp_coordinate_le j _).trans (norm_toLp_d1_le c1 φ)

/-- Scalar nested-derivative `L²` bounds: order two. -/
theorem norm_toLp_scalar_d2_le (c1 c2 j : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (r3SchwartzCoordinate j φ))).toLp 2 :
        Lp ℂ 2 (volume : Measure R3))‖ ≤
      (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by
  rw [lineDerivOp_r3SchwartzCoordinate, lineDerivOp_r3SchwartzCoordinate]
  exact (norm_toLp_coordinate_le j _).trans (norm_toLp_d2_le c1 c2 φ)

/-- Scalar nested-derivative `L²` bounds: order three. -/
theorem norm_toLp_scalar_d3_le (c1 c2 c3 j : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (∂_{r3StdBasis c3}
          (r3SchwartzCoordinate j φ)))).toLp 2 :
        Lp ℂ 2 (volume : Measure R3))‖ ≤
      (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by
  rw [lineDerivOp_r3SchwartzCoordinate, lineDerivOp_r3SchwartzCoordinate,
    lineDerivOp_r3SchwartzCoordinate]
  exact (norm_toLp_coordinate_le j _).trans (norm_toLp_d3_le c1 c2 c3 φ)

/-- Squared-integral form of the scalar order-three bound (for the quartic step). -/
theorem integral_sq_scalar_d3_le (c1 c2 c3 j : Fin 3) (φ : R3SchwartzVelocity) :
    (∫ x : R3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (∂_{r3StdBasis c3}
        (r3SchwartzCoordinate j φ)))) x‖ ^ 2) ≤
      ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) ^ 2 := by
  rw [← sq_norm_toLp_two_scalar]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_scalar_d3_le c1 c2 c3 j φ) 2

/-- Quartic bound for balanced scalar factors: second-order derivatives of a coordinate
have quartic integral at most `9 (‖∇φ‖_{L∞})² ((2π)³‖J³φ‖)²`. -/
theorem quartic_scalar_le (c1 c2 j : Fin 3) (φ : R3SchwartzVelocity) :
    (∫ x : R3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2}
        (r3SchwartzCoordinate j φ))) x‖ ^ 4) ≤
      9 * r3SchwartzGradSup φ ^ 2 * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) ^ 2 := by
  have hgn := r3TSel_gn_quartic (r3SchwartzCoordinate j φ)
    (r3StdBasis c2) (r3StdBasis c1)
    (S := r3SchwartzGradSup φ)
    (fun x => norm_lineDerivOp_coordinate_le_gradSup c2 j φ x)
  refine hgn.trans ?_
  have h1 := integral_sq_scalar_d3_le c1 c1 c2 j φ
  have h2 : (0 : ℝ) ≤ 9 * r3SchwartzGradSup φ ^ 2 := by
    have := r3SchwartzGradSup_nonneg φ
    positivity
  exact mul_le_mul_of_nonneg_left h1 h2

/-- Quartic bound for balanced vector factors, by componentwise reduction. -/
theorem quartic_velocity_le (c1 c2 : Fin 3) (φ : R3SchwartzVelocity) :
    (∫ x : R3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x‖ ^ 4) ≤
      81 * r3SchwartzGradSup φ ^ 2 * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) ^ 2 := by
  have hpt : ∀ x : R3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x‖ ^ 4 ≤
      3 * ∑ j : Fin 3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2}
        (r3SchwartzCoordinate j φ))) x‖ ^ 4 := by
    intro x
    have hcomp : ∀ j : Fin 3,
        (∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (r3SchwartzCoordinate j φ))) x =
          ((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x) j := by
      intro j
      rw [lineDerivOp_r3SchwartzCoordinate, lineDerivOp_r3SchwartzCoordinate]
      rfl
    have hsq : ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x‖ ^ 2 =
        ∑ j : Fin 3, ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x) j‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun j => ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x) j‖ ^ 2)
    have hcard : ((Finset.univ : Finset (Fin 3)).card : ℝ) = 3 := by simp
    calc ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x‖ ^ 4
        = (‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x‖ ^ 2) ^ 2 := by ring
      _ = (∑ j : Fin 3, ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x) j‖ ^ 2) ^ 2 := by
          rw [hsq]
      _ ≤ 3 * ∑ j : Fin 3, (‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x) j‖ ^ 2) ^ 2 := by
          have := hcs
          rw [hcard] at this
          exact_mod_cast this
      _ = 3 * ∑ j : Fin 3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2}
            (r3SchwartzCoordinate j φ))) x‖ ^ 4 := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hcomp j]
          ring
  have hint : (∫ x : R3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2} φ)) x‖ ^ 4) ≤
      ∫ x : R3, 3 * ∑ j : Fin 3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2}
        (r3SchwartzCoordinate j φ))) x‖ ^ 4 := by
    refine integral_mono (integrable_pow4_velocity _) ?_ hpt
    exact (integrable_finsetSum _ fun j _ =>
      integrable_pow4_scalar _).const_mul 3
  refine hint.trans ?_
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => integrable_pow4_scalar _)]
  have hsum : (∑ j : Fin 3, ∫ x : R3, ‖(∂_{r3StdBasis c1} (∂_{r3StdBasis c2}
      (r3SchwartzCoordinate j φ))) x‖ ^ 4) ≤
      ∑ _j : Fin 3,
        9 * r3SchwartzGradSup φ ^ 2 * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) ^ 2 :=
    Finset.sum_le_sum fun j _ => quartic_scalar_le c1 c2 j φ
  refine (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Sup bound for the convection factor `∂ᵢφ`. -/
theorem sup_coordDeriv_le (i : Fin 3) (φ : R3SchwartzVelocity) (x : R3) :
    ‖(r3SchwartzCoordinateDerivative i φ) x‖ ≤ r3SchwartzGradSup φ := by
  rw [r3SchwartzCoordinateDerivative_eq]
  exact norm_lineDerivOp_stdBasis_le_gradSup i φ x


/-! ## Per-term commutator bounds at each order -/

/-- Norm of a `toLp`-image of a Schwartz sum splits subadditively. -/
theorem norm_toLp_add_le (X Y : R3SchwartzVelocity) :
    ‖((X + Y).toLp 2 : R3L2Velocity)‖ ≤
      ‖(X.toLp 2 : R3L2Velocity)‖ + ‖(Y.toLp 2 : R3L2Velocity)‖ := by
  rw [r3Schwartz_toLp_add]
  exact norm_add_le _ _

/-- Triangle bound for a three-term Schwartz sum. -/
theorem norm_toLp_sum3_le {A B C : R3SchwartzVelocity} {a b c : ℝ}
    (hA : ‖(A.toLp 2 : R3L2Velocity)‖ ≤ a)
    (hB : ‖(B.toLp 2 : R3L2Velocity)‖ ≤ b)
    (hC : ‖(C.toLp 2 : R3L2Velocity)‖ ≤ c) :
    ‖((A + B + C).toLp 2 : R3L2Velocity)‖ ≤ a + b + c :=
  (norm_toLp_add_le _ _).trans
    (add_le_add ((norm_toLp_add_le _ _).trans (add_le_add hA hB)) hC)

/-- Triangle bound for the seven-term order-three commutator expansion. -/
theorem norm_toLp_sum7_le {A B C D E F G' : R3SchwartzVelocity}
    {a b c d e f g : ℝ}
    (hA : ‖(A.toLp 2 : R3L2Velocity)‖ ≤ a)
    (hB : ‖(B.toLp 2 : R3L2Velocity)‖ ≤ b)
    (hC : ‖(C.toLp 2 : R3L2Velocity)‖ ≤ c)
    (hD : ‖(D.toLp 2 : R3L2Velocity)‖ ≤ d)
    (hE : ‖(E.toLp 2 : R3L2Velocity)‖ ≤ e)
    (hF : ‖(F.toLp 2 : R3L2Velocity)‖ ≤ f)
    (hG : ‖(G'.toLp 2 : R3L2Velocity)‖ ≤ g) :
    ‖((A + (B + C + D) + (E + F + G')).toLp 2 : R3L2Velocity)‖ ≤
      a + (b + c + d) + (e + f + g) := by
  refine (norm_toLp_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_toLp_add_le _ _).trans
      (add_le_add hA (norm_toLp_sum3_le hB hC hD))
  · exact norm_toLp_sum3_le hE hF hG

/-- Mode-3 packaging: both quartics below `81 G²` give a product bound `9 G`. -/
theorem norm_toLp_smul_le_mode3 (b : R3SchwartzScalar) (y : R3SchwartzVelocity)
    {G : ℝ} (hG0 : 0 ≤ G)
    (hb : (∫ x : R3, ‖b x‖ ^ 4) ≤ 81 * G ^ 2)
    (hy : (∫ x : R3, ‖y x‖ ^ 4) ≤ 81 * G ^ 2) :
    ‖((r3SchwartzSMul b y).toLp 2 : R3L2Velocity)‖ ≤ 9 * G := by
  have h := sq_norm_toLp_smul_le_of_quartics b y (Q := 81 * G ^ 2)
    (by positivity) hb hy
  nlinarith [norm_nonneg ((r3SchwartzSMul b y).toLp 2 : R3L2Velocity)]

/-- Order-one commutator term bound. -/
theorem r3TSel_term_bound_one (c1 i : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} (r3SchwartzSMul (r3SchwartzCoordinate i φ)
          (r3SchwartzCoordinateDerivative i φ)) -
        r3SchwartzSMul (r3SchwartzCoordinate i φ)
          (∂_{r3StdBasis c1} (r3SchwartzCoordinateDerivative i φ))).toLp 2 :
        R3L2Velocity)‖ ≤
      31 * (r3SchwartzGradSup φ *
        ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) := by
  rw [smul_commutator_one]
  have hgs0 := r3SchwartzGradSup_nonneg φ
  have hK0 : (0 : ℝ) ≤ (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by positivity
  have h1 : ‖((r3SchwartzSMul (∂_{r3StdBasis c1} (r3SchwartzCoordinate i φ))
      (r3SchwartzCoordinateDerivative i φ)).toLp 2 : R3L2Velocity)‖ ≤
      r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) := by
    refine norm_toLp_smul_le_sup_left _ _
      (fun x => norm_lineDerivOp_coordinate_le_gradSup c1 i φ x) hK0 ?_
    rw [r3SchwartzCoordinateDerivative_eq]
    exact norm_toLp_d1_le i φ
  refine h1.trans ?_
  nlinarith [mul_nonneg hgs0 hK0]

/-- Order-two commutator term bound. -/
theorem r3TSel_term_bound_two (c1 c2 i : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (r3SchwartzSMul
          (r3SchwartzCoordinate i φ) (r3SchwartzCoordinateDerivative i φ))) -
        r3SchwartzSMul (r3SchwartzCoordinate i φ)
          (∂_{r3StdBasis c1} (∂_{r3StdBasis c2}
            (r3SchwartzCoordinateDerivative i φ)))).toLp 2 :
        R3L2Velocity)‖ ≤
      31 * (r3SchwartzGradSup φ *
        ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) := by
  rw [smul_commutator_two]
  have hgs0 := r3SchwartzGradSup_nonneg φ
  have hK0 : (0 : ℝ) ≤ (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by positivity
  have hG0 : (0 : ℝ) ≤ r3SchwartzGradSup φ *
      ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) := mul_nonneg hgs0 hK0
  have hT1 : ‖((r3SchwartzSMul
      (∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (r3SchwartzCoordinate i φ)))
      (r3SchwartzCoordinateDerivative i φ)).toLp 2 : R3L2Velocity)‖ ≤
      r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) :=
    norm_toLp_smul_le_sup_right _ _
      (fun x => sup_coordDeriv_le i φ x) hK0
      (norm_toLp_scalar_d2_le c1 c2 i φ)
  have hT2 : ‖((r3SchwartzSMul (∂_{r3StdBasis c2} (r3SchwartzCoordinate i φ))
      (∂_{r3StdBasis c1} (r3SchwartzCoordinateDerivative i φ))).toLp 2 :
        R3L2Velocity)‖ ≤
      r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) := by
    refine norm_toLp_smul_le_sup_left _ _
      (fun x => norm_lineDerivOp_coordinate_le_gradSup c2 i φ x) hK0 ?_
    rw [r3SchwartzCoordinateDerivative_eq]
    exact norm_toLp_d2_le c1 i φ
  have hT3 : ‖((r3SchwartzSMul (∂_{r3StdBasis c1} (r3SchwartzCoordinate i φ))
      (∂_{r3StdBasis c2} (r3SchwartzCoordinateDerivative i φ))).toLp 2 :
        R3L2Velocity)‖ ≤
      r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) := by
    refine norm_toLp_smul_le_sup_left _ _
      (fun x => norm_lineDerivOp_coordinate_le_gradSup c1 i φ x) hK0 ?_
    rw [r3SchwartzCoordinateDerivative_eq]
    exact norm_toLp_d2_le c2 i φ
  refine (norm_toLp_sum3_le hT1 hT2 hT3).trans ?_
  linarith

set_option maxHeartbeats 1600000 in
/-- Order-three commutator term bound. -/
theorem r3TSel_term_bound_three (c1 c2 c3 i : Fin 3) (φ : R3SchwartzVelocity) :
    ‖((∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (∂_{r3StdBasis c3} (r3SchwartzSMul
          (r3SchwartzCoordinate i φ) (r3SchwartzCoordinateDerivative i φ)))) -
        r3SchwartzSMul (r3SchwartzCoordinate i φ)
          (∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (∂_{r3StdBasis c3}
            (r3SchwartzCoordinateDerivative i φ))))).toLp 2 :
        R3L2Velocity)‖ ≤
      31 * (r3SchwartzGradSup φ *
        ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) := by
  rw [smul_commutator_three]
  have hgs0 := r3SchwartzGradSup_nonneg φ
  have hK0 : (0 : ℝ) ≤ (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by positivity
  have hG0 : (0 : ℝ) ≤ r3SchwartzGradSup φ *
      ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) := mul_nonneg hgs0 hK0
  have hquartS : ∀ d1 d2 : Fin 3,
      (∫ x : R3, ‖(∂_{r3StdBasis d1} (∂_{r3StdBasis d2}
        (r3SchwartzCoordinate i φ))) x‖ ^ 4) ≤
        81 * (r3SchwartzGradSup φ *
          ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) ^ 2 := by
    intro d1 d2
    refine (quartic_scalar_le d1 d2 i φ).trans ?_
    have h1 : (r3SchwartzGradSup φ *
        ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) ^ 2 =
        r3SchwartzGradSup φ ^ 2 *
          ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) ^ 2 := by ring
    rw [h1]
    nlinarith [mul_nonneg (sq_nonneg (r3SchwartzGradSup φ))
      (sq_nonneg ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖))]
  have hquartV : ∀ d1 : Fin 3,
      (∫ x : R3, ‖(∂_{r3StdBasis d1}
        (r3SchwartzCoordinateDerivative i φ)) x‖ ^ 4) ≤
        81 * (r3SchwartzGradSup φ *
          ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) ^ 2 := by
    intro d1
    have h1 : (∫ x : R3, ‖(∂_{r3StdBasis d1}
        (r3SchwartzCoordinateDerivative i φ)) x‖ ^ 4) =
        ∫ x : R3, ‖(∂_{r3StdBasis d1} (∂_{r3StdBasis i} φ)) x‖ ^ 4 := by
      rw [r3SchwartzCoordinateDerivative_eq]
    rw [h1]
    refine (quartic_velocity_le d1 i φ).trans ?_
    have h2 : (r3SchwartzGradSup φ *
        ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) ^ 2 =
        r3SchwartzGradSup φ ^ 2 *
          ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) ^ 2 := by ring
    rw [h2]
    exact le_of_eq (by ring)
  have hT1 : ‖((r3SchwartzSMul (∂_{r3StdBasis c1} (∂_{r3StdBasis c2}
      (∂_{r3StdBasis c3} (r3SchwartzCoordinate i φ))))
      (r3SchwartzCoordinateDerivative i φ)).toLp 2 : R3L2Velocity)‖ ≤
      r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) :=
    norm_toLp_smul_le_sup_right _ _
      (fun x => sup_coordDeriv_le i φ x) hK0
      (norm_toLp_scalar_d3_le c1 c2 c3 i φ)
  have hT2 : ‖((r3SchwartzSMul
      (∂_{r3StdBasis c2} (∂_{r3StdBasis c3} (r3SchwartzCoordinate i φ)))
      (∂_{r3StdBasis c1} (r3SchwartzCoordinateDerivative i φ))).toLp 2 :
        R3L2Velocity)‖ ≤
      9 * (r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) :=
    norm_toLp_smul_le_mode3 _ _ hG0 (hquartS c2 c3) (hquartV c1)
  have hT3 : ‖((r3SchwartzSMul
      (∂_{r3StdBasis c1} (∂_{r3StdBasis c3} (r3SchwartzCoordinate i φ)))
      (∂_{r3StdBasis c2} (r3SchwartzCoordinateDerivative i φ))).toLp 2 :
        R3L2Velocity)‖ ≤
      9 * (r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) :=
    norm_toLp_smul_le_mode3 _ _ hG0 (hquartS c1 c3) (hquartV c2)
  have hT4 : ‖((r3SchwartzSMul
      (∂_{r3StdBasis c1} (∂_{r3StdBasis c2} (r3SchwartzCoordinate i φ)))
      (∂_{r3StdBasis c3} (r3SchwartzCoordinateDerivative i φ))).toLp 2 :
        R3L2Velocity)‖ ≤
      9 * (r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖)) :=
    norm_toLp_smul_le_mode3 _ _ hG0 (hquartS c1 c2) (hquartV c3)
  have hT5 : ‖((r3SchwartzSMul (∂_{r3StdBasis c3} (r3SchwartzCoordinate i φ))
      (∂_{r3StdBasis c1} (∂_{r3StdBasis c2}
        (r3SchwartzCoordinateDerivative i φ)))).toLp 2 : R3L2Velocity)‖ ≤
      r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) := by
    refine norm_toLp_smul_le_sup_left _ _
      (fun x => norm_lineDerivOp_coordinate_le_gradSup c3 i φ x) hK0 ?_
    rw [r3SchwartzCoordinateDerivative_eq]
    exact norm_toLp_d3_le c1 c2 i φ
  have hT6 : ‖((r3SchwartzSMul (∂_{r3StdBasis c2} (r3SchwartzCoordinate i φ))
      (∂_{r3StdBasis c1} (∂_{r3StdBasis c3}
        (r3SchwartzCoordinateDerivative i φ)))).toLp 2 : R3L2Velocity)‖ ≤
      r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) := by
    refine norm_toLp_smul_le_sup_left _ _
      (fun x => norm_lineDerivOp_coordinate_le_gradSup c2 i φ x) hK0 ?_
    rw [r3SchwartzCoordinateDerivative_eq]
    exact norm_toLp_d3_le c1 c3 i φ
  have hT7 : ‖((r3SchwartzSMul (∂_{r3StdBasis c1} (r3SchwartzCoordinate i φ))
      (∂_{r3StdBasis c2} (∂_{r3StdBasis c3}
        (r3SchwartzCoordinateDerivative i φ)))).toLp 2 : R3L2Velocity)‖ ≤
      r3SchwartzGradSup φ * ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) := by
    refine norm_toLp_smul_le_sup_left _ _
      (fun x => norm_lineDerivOp_coordinate_le_gradSup c1 i φ x) hK0 ?_
    rw [r3SchwartzCoordinateDerivative_eq]
    exact norm_toLp_d3_le c2 c3 i φ
  refine (norm_toLp_sum7_le hT1 hT2 hT3 hT4 hT5 hT6 hT7).trans ?_
  linarith


/-! ## SEL-4 discharged -/

set_option maxHeartbeats 1600000 in
/-- **SEL-4 discharged**: the BKM derivative-tuple commutator estimate holds with the
explicit (unoptimized) constant `C = 93 (2π)³`. -/
theorem r3TSel_katoPonceCommutator :
    ∃ C : ℝ, 0 ≤ C ∧ R3TSelKatoPonceCommutator C := by
  refine ⟨93 * (2 * π) ^ 3, by positivity, ?_⟩
  intro n hn v φ
  have hgs0 := r3SchwartzGradSup_nonneg φ
  have hK0 : (0 : ℝ) ≤ (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by positivity
  interval_cases n
  · -- order zero: the commutator vanishes
    have h0 : (∂^{fun i : Fin 0 => r3StdBasis (v i)} (r3SchwartzConvection φ φ) -
        r3SchwartzConvection φ (∂^{fun i : Fin 0 => r3StdBasis (v i)} φ)) = 0 := by
      show (r3SchwartzConvection φ φ - r3SchwartzConvection φ φ) = 0
      exact sub_self _
    rw [h0]
    have hz : ((0 : R3SchwartzVelocity).toLp 2 : R3L2Velocity) = 0 := by
      apply MeasureTheory.Lp.ext
      filter_upwards [(0 : R3SchwartzVelocity).coeFn_toLp 2 (volume : Measure R3),
        MeasureTheory.Lp.coeFn_zero R3C 2 (volume : Measure R3)] with x h1 h2
      rw [h1, h2]
      rfl
    rw [hz, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg hgs0 (norm_nonneg _))
  · -- order one
    have hred : ∀ ψ : R3SchwartzVelocity,
        ∂^{fun i : Fin 1 => r3StdBasis (v i)} ψ = ∂_{r3StdBasis (v 0)} ψ :=
      fun ψ => rfl
    have hswap : ∀ i : Fin 3,
        r3SchwartzCoordinateDerivative i (∂_{r3StdBasis (v 0)} φ) =
          ∂_{r3StdBasis (v 0)} (r3SchwartzCoordinateDerivative i φ) := by
      intro i
      rw [r3SchwartzCoordinateDerivative_eq,
        lineDerivOp_comm (r3StdBasis i) (r3StdBasis (v 0)),
        ← r3SchwartzCoordinateDerivative_eq i φ]
    have hA : ∂_{r3StdBasis (v 0)} (r3SchwartzConvection φ φ) =
        ∂_{r3StdBasis (v 0)} (r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
          (r3SchwartzCoordinateDerivative 0 φ)) +
        ∂_{r3StdBasis (v 0)} (r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
          (r3SchwartzCoordinateDerivative 1 φ)) +
        ∂_{r3StdBasis (v 0)} (r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
          (r3SchwartzCoordinateDerivative 2 φ)) := by
      rw [r3SchwartzConvection_eq_sum_smul, Fin.sum_univ_three]
      simp only [lineDerivOp_add]
    have hB : r3SchwartzConvection φ (∂_{r3StdBasis (v 0)} φ) =
        r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
          (∂_{r3StdBasis (v 0)} (r3SchwartzCoordinateDerivative 0 φ)) +
        r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
          (∂_{r3StdBasis (v 0)} (r3SchwartzCoordinateDerivative 1 φ)) +
        r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
          (∂_{r3StdBasis (v 0)} (r3SchwartzCoordinateDerivative 2 φ)) := by
      rw [r3SchwartzConvection_eq_sum_smul, Fin.sum_univ_three,
        hswap 0, hswap 1, hswap 2]
    have hdiff : ∂^{fun i : Fin 1 => r3StdBasis (v i)} (r3SchwartzConvection φ φ) -
        r3SchwartzConvection φ (∂^{fun i : Fin 1 => r3StdBasis (v i)} φ) =
        (∂_{r3StdBasis (v 0)} (r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
            (r3SchwartzCoordinateDerivative 0 φ)) -
          r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
            (∂_{r3StdBasis (v 0)} (r3SchwartzCoordinateDerivative 0 φ))) +
        (∂_{r3StdBasis (v 0)} (r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
            (r3SchwartzCoordinateDerivative 1 φ)) -
          r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
            (∂_{r3StdBasis (v 0)} (r3SchwartzCoordinateDerivative 1 φ))) +
        (∂_{r3StdBasis (v 0)} (r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
            (r3SchwartzCoordinateDerivative 2 φ)) -
          r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
            (∂_{r3StdBasis (v 0)} (r3SchwartzCoordinateDerivative 2 φ))) := by
      rw [hred (r3SchwartzConvection φ φ), hred φ, hA, hB]
      abel
    rw [hdiff]
    refine (norm_toLp_sum3_le (r3TSel_term_bound_one (v 0) 0 φ)
      (r3TSel_term_bound_one (v 0) 1 φ) (r3TSel_term_bound_one (v 0) 2 φ)).trans ?_
    exact le_of_eq (by ring)
  · -- order two
    have hred : ∀ ψ : R3SchwartzVelocity,
        ∂^{fun i : Fin 2 => r3StdBasis (v i)} ψ =
          ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} ψ) :=
      fun ψ => rfl
    have hswap : ∀ i : Fin 3,
        r3SchwartzCoordinateDerivative i
            (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} φ)) =
          ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
            (r3SchwartzCoordinateDerivative i φ)) := by
      intro i
      rw [r3SchwartzCoordinateDerivative_eq,
        lineDerivOp_comm (r3StdBasis i) (r3StdBasis (v 0)),
        lineDerivOp_comm (r3StdBasis i) (r3StdBasis (v 1)),
        ← r3SchwartzCoordinateDerivative_eq i φ]
    have hA : ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
        (r3SchwartzConvection φ φ)) =
        ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
          (r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
            (r3SchwartzCoordinateDerivative 0 φ))) +
        ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
          (r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
            (r3SchwartzCoordinateDerivative 1 φ))) +
        ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
          (r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
            (r3SchwartzCoordinateDerivative 2 φ))) := by
      rw [r3SchwartzConvection_eq_sum_smul, Fin.sum_univ_three]
      simp only [lineDerivOp_add]
    have hB : r3SchwartzConvection φ
        (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} φ)) =
        r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
          (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
            (r3SchwartzCoordinateDerivative 0 φ))) +
        r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
          (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
            (r3SchwartzCoordinateDerivative 1 φ))) +
        r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
          (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
            (r3SchwartzCoordinateDerivative 2 φ))) := by
      rw [r3SchwartzConvection_eq_sum_smul, Fin.sum_univ_three,
        hswap 0, hswap 1, hswap 2]
    have hdiff : ∂^{fun i : Fin 2 => r3StdBasis (v i)} (r3SchwartzConvection φ φ) -
        r3SchwartzConvection φ (∂^{fun i : Fin 2 => r3StdBasis (v i)} φ) =
        (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
            (r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
              (r3SchwartzCoordinateDerivative 0 φ))) -
          r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
            (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
              (r3SchwartzCoordinateDerivative 0 φ)))) +
        (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
            (r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
              (r3SchwartzCoordinateDerivative 1 φ))) -
          r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
            (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
              (r3SchwartzCoordinateDerivative 1 φ)))) +
        (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
            (r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
              (r3SchwartzCoordinateDerivative 2 φ))) -
          r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
            (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)}
              (r3SchwartzCoordinateDerivative 2 φ)))) := by
      rw [hred (r3SchwartzConvection φ φ), hred φ, hA, hB]
      abel
    rw [hdiff]
    refine (norm_toLp_sum3_le (r3TSel_term_bound_two (v 0) (v 1) 0 φ)
      (r3TSel_term_bound_two (v 0) (v 1) 1 φ)
      (r3TSel_term_bound_two (v 0) (v 1) 2 φ)).trans ?_
    exact le_of_eq (by ring)
  · -- order three
    have hred : ∀ ψ : R3SchwartzVelocity,
        ∂^{fun i : Fin 3 => r3StdBasis (v i)} ψ =
          ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)} ψ)) :=
      fun ψ => rfl
    have hswap : ∀ i : Fin 3,
        r3SchwartzCoordinateDerivative i (∂_{r3StdBasis (v 0)}
            (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)} φ))) =
          ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
            (r3SchwartzCoordinateDerivative i φ))) := by
      intro i
      rw [r3SchwartzCoordinateDerivative_eq,
        lineDerivOp_comm (r3StdBasis i) (r3StdBasis (v 0)),
        lineDerivOp_comm (r3StdBasis i) (r3StdBasis (v 1)),
        lineDerivOp_comm (r3StdBasis i) (r3StdBasis (v 2)),
        ← r3SchwartzCoordinateDerivative_eq i φ]
    have hA : ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
        (r3SchwartzConvection φ φ))) =
        ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
          (r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
            (r3SchwartzCoordinateDerivative 0 φ)))) +
        ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
          (r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
            (r3SchwartzCoordinateDerivative 1 φ)))) +
        ∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
          (r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
            (r3SchwartzCoordinateDerivative 2 φ)))) := by
      rw [r3SchwartzConvection_eq_sum_smul, Fin.sum_univ_three]
      simp only [lineDerivOp_add]
    have hB : r3SchwartzConvection φ (∂_{r3StdBasis (v 0)}
        (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)} φ))) =
        r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
          (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
            (r3SchwartzCoordinateDerivative 0 φ)))) +
        r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
          (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
            (r3SchwartzCoordinateDerivative 1 φ)))) +
        r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
          (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
            (r3SchwartzCoordinateDerivative 2 φ)))) := by
      rw [r3SchwartzConvection_eq_sum_smul, Fin.sum_univ_three,
        hswap 0, hswap 1, hswap 2]
    have hdiff : ∂^{fun i : Fin 3 => r3StdBasis (v i)} (r3SchwartzConvection φ φ) -
        r3SchwartzConvection φ (∂^{fun i : Fin 3 => r3StdBasis (v i)} φ) =
        (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
            (r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
              (r3SchwartzCoordinateDerivative 0 φ)))) -
          r3SchwartzSMul (r3SchwartzCoordinate 0 φ)
            (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
              (r3SchwartzCoordinateDerivative 0 φ))))) +
        (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
            (r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
              (r3SchwartzCoordinateDerivative 1 φ)))) -
          r3SchwartzSMul (r3SchwartzCoordinate 1 φ)
            (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
              (r3SchwartzCoordinateDerivative 1 φ))))) +
        (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
            (r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
              (r3SchwartzCoordinateDerivative 2 φ)))) -
          r3SchwartzSMul (r3SchwartzCoordinate 2 φ)
            (∂_{r3StdBasis (v 0)} (∂_{r3StdBasis (v 1)} (∂_{r3StdBasis (v 2)}
              (r3SchwartzCoordinateDerivative 2 φ))))) := by
      rw [hred (r3SchwartzConvection φ φ), hred φ, hA, hB]
      abel
    rw [hdiff]
    refine (norm_toLp_sum3_le (r3TSel_term_bound_three (v 0) (v 1) (v 2) 0 φ)
      (r3TSel_term_bound_three (v 0) (v 1) (v 2) 1 φ)
      (r3TSel_term_bound_three (v 0) (v 1) (v 2) 2 φ)).trans ?_
    exact le_of_eq (by ring)

end

end MNS2
