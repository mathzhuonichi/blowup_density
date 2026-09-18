import NSFormalization.Section3.T11.LocalExistence
import NSFormalization.Section3.T10.Leray
import NSFormalization.Paper1.PeriodicInverseWeightSummable
import NSFormalization.Paper1.PeriodicWeightShift

/-! # Bounded realization of the periodic convection convolution

A discrete Cauchy–Schwarz argument bounds the squared convolution kernel by
`32 * (W(l)⁻³ + W(k-l)⁻³)`. The lattice inverse-cube theorem makes its sum
uniform in the output frequency. Reindexing the remaining nonnegative double
sum gives the product of the two ℓ² energies. Thus no finite-support hypothesis,
density argument, or residual analytic input is needed.

The real condition is proved by conjugation and reflection of the absolutely
convergent series. The canonical Leray contraction then preserves the bound;
`LinearMap.mkContinuous₂` gives the exact real bilinear realization.
-/
noncomputable section
namespace NSFormalization.Section3.T11
open NSFormalization.Section3.T10
open scoped BigOperators ENNReal

local instance convolutionNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance convolutionNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

private lemma weight_pos (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  positivity

private lemma inverse_weight_sq (k : PeriodicFrequency) :
    (periodicFrequencyWeight k ^ (-(3 : ℝ) / 2)) ^ 2 =
      (periodicFrequencyWeight k ^ (3 : ℕ))⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (weight_pos k).le]
  norm_num [Real.rpow_neg (weight_pos k).le]

private lemma derivative_sq_le (j : Fin 3) (k : PeriodicFrequency) :
    ‖periodicDerivativeSymbol j k‖ ^ 2 ≤ periodicFrequencyWeight k := by
  have h := Finset.single_le_sum (f := fun i : Fin 3 ↦ (k i : ℝ)^2)
    (fun i _ ↦ sq_nonneg _) (Finset.mem_univ j)
  simp only [periodicDerivativeSymbol, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, mul_one, Complex.norm_intCast, mul_pow, sq_abs]
  unfold periodicFrequencyWeight
  nlinarith [sq_nonneg Real.pi]

private lemma weight_cube_shift (k l : PeriodicFrequency) :
    periodicFrequencyWeight k ^ 3 ≤
      32 * (periodicFrequencyWeight l ^ 3 + periodicFrequencyWeight (k-l) ^ 3) := by
  have h := NSFormalization.Paper1.PeriodicWeightShift.weight_add_le l (k-l)
  rw [add_sub_cancel] at h
  rw [← torus_weight_eq, ← torus_weight_eq, ← torus_weight_eq] at h
  have ha := (weight_pos l).le
  have hb := (weight_pos (k-l)).le
  have hc := (weight_pos k).le
  have h' : periodicFrequencyWeight k ≤
      2 * (periodicFrequencyWeight l + periodicFrequencyWeight (k-l)) := by linarith
  have hp := pow_le_pow_left₀ hc h' 3
  have hh := mul_nonneg (sq_nonneg (periodicFrequencyWeight l - periodicFrequencyWeight (k-l)))
    (add_nonneg ha hb)
  nlinarith

/-- Scalar coefficient of one differentiated tensor entry, with the exact input
and output Sobolev weights. -/
def torusScalarConvection (a b : PeriodicScalarData) (j : Fin 3)
    (k : PeriodicFrequency) : ℂ :=
  (periodicFrequencyWeight k : ℂ) * periodicDerivativeSymbol j k *
    ∑' l : PeriodicFrequency,
      ((periodicFrequencyWeight l ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * a l *
        ((periodicFrequencyWeight (k-l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * b (k-l)

private def convolutionKernel (j : Fin 3) (k l : PeriodicFrequency) : ℝ :=
  periodicFrequencyWeight k * ‖periodicDerivativeSymbol j k‖ *
    periodicFrequencyWeight l ^ (-(3 : ℝ) / 2) *
      periodicFrequencyWeight (k-l) ^ (-(3 : ℝ) / 2)

private lemma convolutionKernel_nonneg (j : Fin 3) (k l : PeriodicFrequency) :
    0 ≤ convolutionKernel j k l := by
  unfold convolutionKernel
  exact mul_nonneg (mul_nonneg (mul_nonneg (weight_pos k).le (norm_nonneg _))
    (Real.rpow_nonneg (weight_pos l).le _)) (Real.rpow_nonneg (weight_pos (k-l)).le _)

private lemma convolutionKernel_sq_le (j : Fin 3) (k l : PeriodicFrequency) :
    convolutionKernel j k l ^ 2 ≤ 32 *
      ((periodicFrequencyWeight l ^ 3)⁻¹ + (periodicFrequencyWeight (k-l) ^ 3)⁻¹) := by
  simp only [convolutionKernel, mul_pow, inverse_weight_sq]
  have h1 : periodicFrequencyWeight k ^ 2 * ‖periodicDerivativeSymbol j k‖ ^ 2 ≤
      periodicFrequencyWeight k ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left (derivative_sq_le j k)
      (sq_nonneg (periodicFrequencyWeight k))]
  calc
    _ ≤ (32 * (periodicFrequencyWeight l ^ 3 + periodicFrequencyWeight (k-l) ^ 3)) *
        (periodicFrequencyWeight l ^ 3)⁻¹ * (periodicFrequencyWeight (k-l) ^ 3)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (h1.trans (weight_cube_shift k l))
          (inv_nonneg.mpr (pow_nonneg (weight_pos l).le _)))
        (inv_nonneg.mpr (pow_nonneg (weight_pos (k-l)).le _))
    _ = _ := by
      field_simp [(weight_pos l).ne', (weight_pos (k-l)).ne']
      ring

private lemma inverse_weight_summable :
    Summable (fun k : PeriodicFrequency ↦ (periodicFrequencyWeight k ^ 3)⁻¹) := by
  simpa only [torus_weight_eq] using
    NSFormalization.Paper1.PeriodicInverseWeightSummable.summable_inverse_weight_cube

private def convolutionBoundSquared : ℝ :=
  64 * ∑' k : PeriodicFrequency, (periodicFrequencyWeight k ^ 3)⁻¹

private lemma kernel_summable (j : Fin 3) (k : PeriodicFrequency) :
    Summable (fun l ↦ convolutionKernel j k l ^ 2) :=
  ((inverse_weight_summable.add
    (inverse_weight_summable.comp_injective (sub_right_injective (b := k)))).mul_left 32).of_nonneg_of_le
      (fun _ ↦ sq_nonneg _) (convolutionKernel_sq_le j k)

private lemma kernel_sum_le (j : Fin 3) (k : PeriodicFrequency) :
    (∑' l, convolutionKernel j k l ^ 2) ≤ convolutionBoundSquared := by
  have h := (kernel_summable j k).tsum_le_tsum (convolutionKernel_sq_le j k)
    ((inverse_weight_summable.add
      (inverse_weight_summable.comp_injective (sub_right_injective (b := k)))).mul_left 32)
  have hs : Summable (fun l ↦ (periodicFrequencyWeight (k-l) ^ 3)⁻¹) :=
    inverse_weight_summable.comp_injective sub_right_injective
  rw [tsum_mul_left, inverse_weight_summable.tsum_add hs] at h
  rw [show (∑' l, (periodicFrequencyWeight (k-l) ^ 3)⁻¹) =
    ∑' l, (periodicFrequencyWeight l ^ 3)⁻¹ from
    (Equiv.subLeft k).tsum_eq (fun l ↦ (periodicFrequencyWeight l ^ 3)⁻¹)] at h
  unfold convolutionBoundSquared
  linarith

private lemma scalar_energy (a : PeriodicScalarData) :
    Summable (fun k ↦ ‖a k‖ ^ 2) ∧ (∑' k, ‖a k‖ ^ 2) = ‖a‖ ^ 2 := by
  constructor
  · simpa using (lp.memℓp a).summable (by norm_num)
  · simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a).symm

private lemma product_energy (a b : PeriodicScalarData) :
    Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦ ‖a p.2‖ ^ 2 * ‖b (p.1-p.2)‖ ^ 2) ∧
      (∑' k, ∑' l, ‖a l‖ ^ 2 * ‖b (k-l)‖ ^ 2) = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  let convolutionPairEquiv :
      (PeriodicFrequency × PeriodicFrequency) ≃ (PeriodicFrequency × PeriodicFrequency) :=
    { toFun := fun p ↦ (p.2, p.1-p.2)
      invFun := fun p ↦ (p.1+p.2, p.1)
      left_inv := fun p ↦ by ext <;> simp
      right_inv := fun p ↦ by ext <;> simp }
  have hp := (scalar_energy a).1.mul_of_nonneg (scalar_energy b).1
    (fun _ ↦ sq_nonneg _) (fun _ ↦ sq_nonneg _)
  have h : Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦
      ‖a p.2‖ ^ 2 * ‖b (p.1-p.2)‖ ^ 2) :=
    hp.comp_injective (i := fun p : PeriodicFrequency × PeriodicFrequency ↦ (p.2, p.1-p.2))
      convolutionPairEquiv.injective
  refine ⟨h, ?_⟩
  rw [← h.tsum_prod]
  change (∑' p, (fun q : PeriodicFrequency × PeriodicFrequency ↦
    ‖a q.1‖ ^ 2 * ‖b q.2‖ ^ 2) (convolutionPairEquiv p)) = _
  exact (convolutionPairEquiv.tsum_eq (fun q : PeriodicFrequency × PeriodicFrequency ↦
    ‖a q.1‖ ^ 2 * ‖b q.2‖ ^ 2)).trans (hp.tsum_prod.trans (by
      simp only [tsum_mul_left, tsum_mul_right, (scalar_energy a).2, (scalar_energy b).2]))

private lemma scalar_convolution_norm_le (a b : PeriodicScalarData) (j : Fin 3)
    (k : PeriodicFrequency) :
    ‖torusScalarConvection a b j k‖ ^ 2 ≤
      convolutionBoundSquared * ∑' l, ‖a l‖ ^ 2 * ‖b (k-l)‖ ^ 2 := by
  let x : lp (fun _ : PeriodicFrequency ↦ ℝ) 2 :=
    ⟨fun l ↦ ‖a l‖ * ‖b (k-l)‖, memℓp_gen (by
      simpa [Real.norm_eq_abs, mul_pow] using (product_energy a b).1.prod_factor k)⟩
  let w : lp (fun _ : PeriodicFrequency ↦ ℝ) 2 :=
    ⟨convolutionKernel j k, memℓp_gen (by
      simpa [Real.norm_eq_abs] using kernel_summable j k)⟩
  have hh := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by simpa using Real.HolderConjugate.two_two) w x
  have he (l : PeriodicFrequency) :
      ‖(periodicFrequencyWeight k : ℂ) * periodicDerivativeSymbol j k *
        (((periodicFrequencyWeight l ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * a l *
          ((periodicFrequencyWeight (k-l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * b (k-l))‖ =
        ‖w l‖ * ‖x l‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simp only [abs_of_nonneg (weight_pos k).le,
      abs_of_nonneg (Real.rpow_nonneg (weight_pos l).le _),
      abs_of_nonneg (Real.rpow_nonneg (weight_pos (k-l)).le _)]
    change _ = |convolutionKernel j k l| * |‖a l‖ * ‖b (k-l)‖|
    rw [abs_of_nonneg (convolutionKernel_nonneg j k l),
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    dsimp [convolutionKernel]
    ring
  have ht : ‖torusScalarConvection a b j k‖ ≤ ‖w‖ * ‖x‖ := by
    unfold torusScalarConvection
    rw [← tsum_mul_left]
    have hs : Summable (fun l : PeriodicFrequency ↦
        (periodicFrequencyWeight k : ℂ) * periodicDerivativeSymbol j k *
          (((periodicFrequencyWeight l ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * a l *
            ((periodicFrequencyWeight (k-l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * b (k-l))) := by
      apply Summable.of_norm
      simpa only [he] using hh.1
    exact (norm_tsum_le_tsum_norm hs.norm).trans (by simpa only [he] using hh.2)
  have hw : ‖w‖ ^ 2 ≤ convolutionBoundSquared := by
    rw [show ‖w‖ ^ 2 = ∑' l, convolutionKernel j k l ^ 2 by
      simpa [w, Real.norm_eq_abs] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) w]
    exact kernel_sum_le j k
  have hx : ‖x‖ ^ 2 = ∑' l, ‖a l‖ ^ 2 * ‖b (k-l)‖ ^ 2 := by
    simpa [x, Real.norm_eq_abs, mul_pow] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  calc
    _ ≤ (‖w‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ = ‖w‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
    _ ≤ convolutionBoundSquared * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = _ := by rw [hx]

private lemma boundSquared_nonneg : 0 ≤ convolutionBoundSquared := by
  apply mul_nonneg (by norm_num)
  exact tsum_nonneg (fun k ↦ inv_nonneg.mpr (pow_nonneg (weight_pos k).le _))

/-- The complete scalar convolution belongs to ℓ², without a cutoff hypothesis. -/
theorem torusScalarConvection_memℓp (a b : PeriodicScalarData) (j : Fin 3) :
    Memℓp (torusScalarConvection a b j) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact ((product_energy a b).1.prod.mul_left convolutionBoundSquared).of_nonneg_of_le
    (fun _ ↦ sq_nonneg _) (scalar_convolution_norm_le a b j)

/-- Scalar convolution on the actual complete coefficient carrier. -/
def torusScalarConvectionLp (a b : PeriodicScalarData) (j : Fin 3) : PeriodicScalarData :=
  ⟨torusScalarConvection a b j, torusScalarConvection_memℓp a b j⟩

/-- A uniform scalar bilinear estimate. -/
theorem torusScalarConvectionLp_norm_le (a b : PeriodicScalarData) (j : Fin 3) :
    ‖torusScalarConvectionLp a b j‖ ≤ Real.sqrt convolutionBoundSquared * ‖a‖ * ‖b‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (by positivity)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have h := ((torusScalarConvection_memℓp a b j).summable (by norm_num)).tsum_le_tsum
    (show ∀ k, ‖torusScalarConvection a b j k‖ ^ (2 : ℝ≥0∞).toReal ≤
      convolutionBoundSquared * ∑' l, ‖a l‖ ^ 2 * ‖b (k-l)‖ ^ 2 by
      simpa using scalar_convolution_norm_le a b j)
    ((product_energy a b).1.prod.mul_left convolutionBoundSquared)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [tsum_mul_left, (product_energy a b).2] at h
  simpa only [mul_pow, Real.sq_sqrt boundSquared_nonneg, torusScalarConvectionLp, mul_assoc] using h

private lemma convection_eq_sum (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbol A B i k = ∑ j : Fin 3, torusScalarConvection (A.1 j) (B.1 i) j k := by
  simp only [torusConvectionSymbol, torusScalarConvection, Finset.mul_sum, mul_assoc]

private lemma convection_real (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbol A B i (-k) = star (torusConvectionSymbol A B i k) := by
  have hc (j : Fin 3) :
      (∑' l : PeriodicFrequency,
        (((periodicFrequencyWeight l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * A.1 j l *
          (((periodicFrequencyWeight (-k-l)) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * B.1 i (-k-l)) =
      star (∑' l : PeriodicFrequency,
        (((periodicFrequencyWeight l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * A.1 j l *
          (((periodicFrequencyWeight (k-l)) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * B.1 i (k-l)) := by
    rw [← (Equiv.neg PeriodicFrequency).tsum_eq]
    simp only [Equiv.neg_apply, show ∀ l : PeriodicFrequency, -k - -l = -(k-l) by intro l; abel,
      torus_weight_neg]
    have hA : ∀ l, A.1 j (-l) = star (A.1 j l) := A.2 j
    have hB : ∀ l, B.1 i (-l) = star (B.1 i l) := B.2 i
    simp only [hA, hB, Complex.star_def]
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro l
    simp only [map_mul, Complex.conj_ofReal]
  unfold torusConvectionSymbol
  rw [torus_weight_neg]
  simp only [hc, Complex.star_def, map_mul, map_sum, Complex.conj_ofReal]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [periodicDerivativeSymbol, map_mul, map_ofNat]

/-- The unprojected H² convection datum. -/
def torusConvectionDatum (A B : PeriodicSobolev 3) : PeriodicSobolev 2 :=
  ⟨WithLp.toLp 2 (fun i ↦ ∑ j : Fin 3, torusScalarConvectionLp (A.1 j) (B.1 i) j), by
    intro i k
    change (∑ j : Fin 3, torusScalarConvectionLp (A.1 j) (B.1 i) j) (-k) =
      star ((∑ j : Fin 3, torusScalarConvectionLp (A.1 j) (B.1 i) j) k)
    simpa only [lp.coeFn_sum, Finset.sum_apply, torusScalarConvectionLp,
      ← convection_eq_sum] using convection_real A B i k⟩

theorem torusConvectionDatum_coeff (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvectionDatum A B).1 i k = torusConvectionSymbol A B i k := by
  simp only [torusConvectionDatum, WithLp.ofLp_toLp, lp.coeFn_sum, Finset.sum_apply,
    torusScalarConvectionLp, convection_eq_sum]

/-- A convenient explicit uniform bilinear constant:
`9 * sqrt (64 * ∑' k, W(k)⁻³)`. No optimality is claimed. -/
def torusConvolutionConstant : ℝ := 9 * Real.sqrt convolutionBoundSquared

-- Finite vector norms require elaboration of the nested lp/submodule carriers.
set_option maxHeartbeats 400000 in
theorem torusConvectionDatum_norm_le (A B : PeriodicSobolev 3) :
    ‖torusConvectionDatum A B‖ ≤ torusConvolutionConstant * ‖A‖ * ‖B‖ := by
  let D := Real.sqrt convolutionBoundSquared * ‖A‖ * ‖B‖
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg A)) (norm_nonneg B)
  have hi (i : Fin 3) : ‖(torusConvectionDatum A B).1 i‖ ≤ 3 * D := by
    change ‖∑ j : Fin 3, torusScalarConvectionLp (A.1 j) (B.1 i) j‖ ≤ _
    calc
      _ ≤ ∑ j : Fin 3, ‖torusScalarConvectionLp (A.1 j) (B.1 i) j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, D := by
        apply Finset.sum_le_sum
        intro j _
        apply (torusScalarConvectionLp_norm_le _ _ _).trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le A.1 j)
          (Real.sqrt_nonneg _)) (PiLp.norm_apply_le B.1 i) (norm_nonneg _) (by positivity)
      _ = 3 * D := by simp
  have hsq : ‖torusConvectionDatum A B‖ ^ 2 ≤ 3 * (3 * D) ^ 2 := by
    change ‖(torusConvectionDatum A B).1‖ ^ 2 ≤ _
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _i : Fin 3, (3 * D) ^ 2 :=
        Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hi i) 2)
      _ = _ := by simp
  change ‖torusConvectionDatum A B‖ ≤ 9 * Real.sqrt convolutionBoundSquared * ‖A‖ * ‖B‖
  have he : 9 * Real.sqrt convolutionBoundSquared * ‖A‖ * ‖B‖ = 9 * D := by dsimp only [D]; ring
  rw [he]
  nlinarith [norm_nonneg (torusConvectionDatum A B)]

private lemma convection_add_left (A D B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbol (A+D) B i k = torusConvectionSymbol A B i k + torusConvectionSymbol D B i k := by
  unfold torusConvectionSymbol
  have h (j : Fin 3) := ((torusConvolution_summable A B i j k).of_norm).tsum_add
    ((torusConvolution_summable D B i j k).of_norm)
  simp only [Submodule.coe_add, PiLp.add_apply, lp.coeFn_add, Pi.add_apply,
    mul_add, add_mul, h, Finset.sum_add_distrib]

private lemma convection_add_right (A B D : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbol A (B+D) i k = torusConvectionSymbol A B i k + torusConvectionSymbol A D i k := by
  unfold torusConvectionSymbol
  have h (j : Fin 3) := ((torusConvolution_summable A B i j k).of_norm).tsum_add
    ((torusConvolution_summable A D i j k).of_norm)
  simp only [Submodule.coe_add, PiLp.add_apply, lp.coeFn_add, Pi.add_apply,
    mul_add, h, Finset.sum_add_distrib]

private lemma convection_smul_left (c : ℝ) (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbol (c • A) B i k = (c : ℂ) * torusConvectionSymbol A B i k := by
  unfold torusConvectionSymbol
  simp only [Submodule.coe_smul, PiLp.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.real_smul, mul_left_comm, mul_assoc, tsum_mul_left, Finset.mul_sum]

private lemma convection_smul_right (c : ℝ) (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbol A (c • B) i k = (c : ℂ) * torusConvectionSymbol A B i k := by
  unfold torusConvectionSymbol
  simp only [Submodule.coe_smul, PiLp.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.real_smul, mul_left_comm, mul_assoc, tsum_mul_left, Finset.mul_sum]

/-- Leray projection of the complete, unprojected convolution datum. -/
def torusProjectedConvectionDatum (A B : PeriodicSobolev 3) : PeriodicSobolev 2 :=
  Classical.choose (leray_exists_contraction 2 (torusConvectionDatum A B))

theorem torusProjectedConvectionDatum_coeff (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    (torusProjectedConvectionDatum A B).1 i k = torusProjectedConvectionSymbol A B i k := by
  have h := (Classical.choose_spec (leray_exists_contraction 2 (torusConvectionDatum A B))).1 i k
  simpa only [torusProjectedConvectionDatum, periodicLeray, torusProjectedConvectionSymbol,
    torusConvectionDatum_coeff] using h

theorem torusProjectedConvectionDatum_norm_le (A B : PeriodicSobolev 3) :
    ‖torusProjectedConvectionDatum A B‖ ≤ torusConvolutionConstant * ‖A‖ * ‖B‖ :=
  (Classical.choose_spec (leray_exists_contraction 2 (torusConvectionDatum A B))).2.1.trans
    (torusConvectionDatum_norm_le A B)

private lemma datum_ext {s : ℝ} {A B : PeriodicSobolev s}
    (h : ∀ i k, A.1 i k = B.1 i k) : A = B := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  exact lp.ext (funext (h i))

/-- The exact projected convolution as a real bilinear map before bundling continuity. -/
def torusConvolutionLinearMap :
    PeriodicSobolev 3 →ₗ[ℝ] PeriodicSobolev 3 →ₗ[ℝ] PeriodicSobolev 2 :=
  LinearMap.mk₂ ℝ torusProjectedConvectionDatum
    (by
      intro A D B
      apply datum_ext
      intro i k
      change (torusProjectedConvectionDatum (A+D) B).1 i k =
        (torusProjectedConvectionDatum A B).1 i k + (torusProjectedConvectionDatum D B).1 i k
      simp only [torusProjectedConvectionDatum_coeff, torusProjectedConvectionSymbol, convection_add_left]
      split_ifs <;> simp only [mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro c A B
      apply datum_ext
      intro i k
      change (torusProjectedConvectionDatum (c • A) B).1 i k =
        (c : ℂ) * (torusProjectedConvectionDatum A B).1 i k
      simp only [torusProjectedConvectionDatum_coeff, torusProjectedConvectionSymbol, convection_smul_left]
      split_ifs <;> simp only [Finset.mul_sum, mul_sub, mul_left_comm])
    (by
      intro A B D
      apply datum_ext
      intro i k
      change (torusProjectedConvectionDatum A (B+D)).1 i k =
        (torusProjectedConvectionDatum A B).1 i k + (torusProjectedConvectionDatum A D).1 i k
      simp only [torusProjectedConvectionDatum_coeff, torusProjectedConvectionSymbol, convection_add_right]
      split_ifs <;> simp only [mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro c A B
      apply datum_ext
      intro i k
      change (torusProjectedConvectionDatum A (c • B)).1 i k =
        (c : ℂ) * (torusProjectedConvectionDatum A B).1 i k
      simp only [torusProjectedConvectionDatum_coeff, torusProjectedConvectionSymbol, convection_smul_right]
      split_ifs <;> simp only [Finset.mul_sum, mul_sub, mul_left_comm])

/-- Bounded real bilinear realization H³ × H³ → H². -/
def torusConvolutionCLM :
    PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2 :=
  torusConvolutionLinearMap.mkContinuous₂ torusConvolutionConstant
    torusProjectedConvectionDatum_norm_le

theorem torusConvolutionCLM_coeff (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM A B).1 i k = torusProjectedConvectionSymbol A B i k :=
  torusProjectedConvectionDatum_coeff A B i k

theorem torusConvolutionCLM_norm_le : ‖torusConvolutionCLM‖ ≤ torusConvolutionConstant := by
  apply LinearMap.mkContinuous₂_norm_le
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- Lane 313's residual input is discharged without an analytic assumption. -/
theorem torusConvolutionInput : TorusConvolutionInput :=
  ⟨torusConvolutionCLM, torusConvolutionCLM_coeff⟩

/-- The exact two-space torus contract is inhabited at every positive viscosity. -/
theorem torusTwoSpaceContract_nonempty' (ν : ℝ) (hν : 0 < ν) :
    Nonempty (TorusTwoSpaceContract ν) :=
  torusTwoSpaceContract_nonempty torusConvolutionInput ν hν

/-- A nonzero datum and nonzero forcing mode test the actual convolution map. -/
theorem torusConvolutionCLM_constants
    (c d : NavierStokes.ProblemStatement.Space) :
    torusConvolutionCLM (torusConstantDatum 3 c) (torusConstantDatum 3 d) = 0 := by
  apply datum_ext
  intro i k
  rw [torusConvolutionCLM_coeff, torusProjectedConvectionSymbol_constants]
  rfl

example : ∃ A B : PeriodicSobolev 3,
    A ≠ 0 ∧ B ≠ 0 ∧ torusConvolutionCLM A B = 0 := by
  let c : NavierStokes.ProblemStatement.Space := WithLp.toLp 2 (fun _ ↦ 1)
  let A := torusConstantDatum 3 c
  have hA : A ≠ 0 := by
    intro h
    have hc := congrArg (fun D : PeriodicSobolev 3 ↦ D.1 (0 : Fin 3) (0 : PeriodicFrequency)) h
    change (1 : ℂ) = 0 at hc
    exact one_ne_zero hc
  exact ⟨A, A, hA, hA, torusConvolutionCLM_constants c c⟩

end NSFormalization.Section3.T11
