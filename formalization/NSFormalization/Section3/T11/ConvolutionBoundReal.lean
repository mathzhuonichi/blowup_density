import NSFormalization.Section3.T11.ConvolutionBound
import NSFormalization.Section3.T11.Persistence

/-! # The projected convection convolution at every real order `r ≥ 3`

Lane 317 realized the projected convection symbol as a bounded real bilinear
map `H³ × H³ → H²` on the canonical weighted carriers.  This module runs the
same discrete Cauchy--Schwarz argument at an arbitrary real order: the input
weights are removed with `W^(-r/2)`, the output weight `W^((r-1)/2)` is
restored, and the Peetre inequality is used with a real exponent,

  `W(k)^r ≤ 4^r (W(l)^r + W(k-l)^r)`,     `W(k) = 1 + 4π²|k|²`,

which follows from `W(k) ≤ 4 max (W l) (W (k-l))` and monotonicity of `rpow`.
The lattice summability of `W^(-r)` is inherited from `W^(-3)` because
`W ≥ 1` and `-r ≤ -3`.  Nothing else changes, so no finite-support hypothesis,
density argument or analytic input appears.

Beyond the bound, the module proves the order-transport identity: the order-`r'`
symbol evaluated on reweighted data is the order-`r` symbol transported by
`W^((r'-r)/2)`.  Specializing `r := 3` identifies the coefficients of the new
map with lane 317's `torusProjectedConvectionSymbol` of the down-reweighted data.
-/
noncomputable section
namespace NSFormalization.Section3.T11
open NSFormalization.Section3.T10
open scoped BigOperators ENNReal

local instance convolutionRealNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance convolutionRealNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. Real-exponent weight arithmetic -/

private lemma weightR_pos (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  positivity

private lemma one_le_weightR (k : PeriodicFrequency) : 1 ≤ periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  have h : 0 ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  linarith

private lemma weightR_rpow_pos (k : PeriodicFrequency) (a : ℝ) :
    0 < periodicFrequencyWeight k ^ a :=
  Real.rpow_pos_of_pos (weightR_pos k) a

/-- Squaring halves the real exponent back. -/
private lemma weightR_half_sq (k : PeriodicFrequency) (a : ℝ) :
    (periodicFrequencyWeight k ^ (a / 2)) ^ (2 : ℕ) = periodicFrequencyWeight k ^ a := by
  rw [← Real.rpow_natCast (periodicFrequencyWeight k ^ (a / 2)) 2,
    ← Real.rpow_mul (weightR_pos k).le]
  congr 1
  push_cast
  ring

/-- Adding real exponents, in the complex coefficient carrier. -/
private lemma ofReal_weightR_mul (k : PeriodicFrequency) (a b : ℝ) :
    ((periodicFrequencyWeight k ^ a : ℝ) : ℂ) * ((periodicFrequencyWeight k ^ b : ℝ) : ℂ)
      = ((periodicFrequencyWeight k ^ (a + b) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add (weightR_pos k)]

/-- `W(k) ≤ 4 max (W l) (W (k-l))`: the triangle inequality on the lattice. -/
private lemma weightR_le_max (k l : PeriodicFrequency) :
    periodicFrequencyWeight k ≤
      4 * max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) := by
  have h := NSFormalization.Paper1.PeriodicWeightShift.weight_add_le l (k - l)
  rw [add_sub_cancel] at h
  rw [← torus_weight_eq, ← torus_weight_eq, ← torus_weight_eq] at h
  have h1 := le_max_left (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))
  have h2 := le_max_right (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))
  linarith

/-- Peetre's inequality at an arbitrary nonnegative real exponent. -/
private lemma weightR_peetre {r : ℝ} (hr : 0 ≤ r) (k l : PeriodicFrequency) :
    periodicFrequencyWeight k ^ r ≤
      (4 : ℝ) ^ r *
        (periodicFrequencyWeight l ^ r + periodicFrequencyWeight (k - l) ^ r) := by
  have hMpos : 0 < max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) :=
    lt_of_lt_of_le (weightR_pos l) (le_max_left _ _)
  have h1 : periodicFrequencyWeight k ^ r ≤
      (4 * max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ r :=
    Real.rpow_le_rpow (weightR_pos k).le (weightR_le_max k l) hr
  have h2 : (4 * max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ r =
      (4 : ℝ) ^ r * (max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ r :=
    Real.mul_rpow (by norm_num) hMpos.le
  have h3 : (max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ r ≤
      periodicFrequencyWeight l ^ r + periodicFrequencyWeight (k - l) ^ r := by
    rcases max_cases (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) with
      ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      linarith [(weightR_rpow_pos (k - l) r).le]
    · rw [he]
      linarith [(weightR_rpow_pos l r).le]
  calc periodicFrequencyWeight k ^ r ≤ _ := h1
    _ = (4 : ℝ) ^ r * (max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ r := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num) r)

/-- Lattice summability of `W^(-r)` for `r ≥ 3`, by comparison with `W^(-3)`. -/
private lemma inverse_weightR_summable {r : ℝ} (hr : 3 ≤ r) :
    Summable (fun k : PeriodicFrequency ↦ periodicFrequencyWeight k ^ (-r)) := by
  apply Summable.of_nonneg_of_le (fun k ↦ (weightR_rpow_pos k _).le)
    (fun k ↦ Real.rpow_le_rpow_of_exponent_le (one_le_weightR k) (by linarith :
      -r ≤ (-3 : ℝ)))
  simpa only [torus_weight_eq] using
    NSFormalization.Paper1.PeriodicInverseWeightSummable.summable_weight_rpow_neg_three

private lemma derivativeR_sq_le (j : Fin 3) (k : PeriodicFrequency) :
    ‖periodicDerivativeSymbol j k‖ ^ 2 ≤ periodicFrequencyWeight k := by
  have h := Finset.single_le_sum (f := fun i : Fin 3 ↦ (k i : ℝ) ^ 2)
    (fun i _ ↦ sq_nonneg _) (Finset.mem_univ j)
  simp only [periodicDerivativeSymbol, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, mul_one, Complex.norm_intCast, mul_pow, sq_abs]
  unfold periodicFrequencyWeight
  nlinarith [sq_nonneg Real.pi]

/-! ## 2. The scalar convolution at real order -/

/-- Scalar coefficient of one differentiated tensor entry at real order `r`.
The two inputs are unweighted by `W^(-r/2)` and the output weight `W^((r-1)/2)`
is restored; at `r = 3` this is lane 317's `torusScalarConvection`. -/
def torusScalarConvectionReal (r : ℝ) (a b : PeriodicScalarData) (j : Fin 3)
    (k : PeriodicFrequency) : ℂ :=
  ((periodicFrequencyWeight k ^ ((r - 1) / 2) : ℝ) : ℂ) * periodicDerivativeSymbol j k *
    ∑' l : PeriodicFrequency,
      ((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * a l *
        ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * b (k - l)

/-- At order three the real-order scalar symbol is lane 317's symbol. -/
theorem torusScalarConvectionReal_three (a b : PeriodicScalarData) (j : Fin 3)
    (k : PeriodicFrequency) :
    torusScalarConvectionReal 3 a b j k = torusScalarConvection a b j k := by
  unfold torusScalarConvectionReal torusScalarConvection
  rw [show ((3 : ℝ) - 1) / 2 = 1 by norm_num, Real.rpow_one]

private def convolutionKernelReal (r : ℝ) (j : Fin 3) (k l : PeriodicFrequency) : ℝ :=
  periodicFrequencyWeight k ^ ((r - 1) / 2) * ‖periodicDerivativeSymbol j k‖ *
    periodicFrequencyWeight l ^ (-r / 2) *
      periodicFrequencyWeight (k - l) ^ (-r / 2)

private lemma convolutionKernelReal_nonneg (r : ℝ) (j : Fin 3) (k l : PeriodicFrequency) :
    0 ≤ convolutionKernelReal r j k l := by
  unfold convolutionKernelReal
  exact mul_nonneg (mul_nonneg (mul_nonneg (weightR_rpow_pos k _).le (norm_nonneg _))
    (weightR_rpow_pos l _).le) (weightR_rpow_pos (k - l) _).le

private lemma convolutionKernelReal_sq_le {r : ℝ} (hr : 3 ≤ r) (j : Fin 3)
    (k l : PeriodicFrequency) :
    convolutionKernelReal r j k l ^ 2 ≤ (4 : ℝ) ^ r *
      (periodicFrequencyWeight l ^ (-r) + periodicFrequencyWeight (k - l) ^ (-r)) := by
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hkey : convolutionKernelReal r j k l ^ 2 =
      (periodicFrequencyWeight k ^ (r - 1) * ‖periodicDerivativeSymbol j k‖ ^ 2) *
        (periodicFrequencyWeight l ^ (-r) * periodicFrequencyWeight (k - l) ^ (-r)) := by
    unfold convolutionKernelReal
    rw [mul_pow, mul_pow, mul_pow, weightR_half_sq, weightR_half_sq, weightR_half_sq]
    ring
  have h1 : periodicFrequencyWeight k ^ (r - 1) * ‖periodicDerivativeSymbol j k‖ ^ 2 ≤
      periodicFrequencyWeight k ^ r := by
    have h := mul_le_mul_of_nonneg_left (derivativeR_sq_le j k) (weightR_rpow_pos k (r - 1)).le
    rwa [← Real.rpow_add_one (weightR_pos k).ne' (r - 1), sub_add_cancel] at h
  have he (m : PeriodicFrequency) :
      periodicFrequencyWeight m ^ r * periodicFrequencyWeight m ^ (-r) = 1 := by
    rw [← Real.rpow_add (weightR_pos m)]
    simp
  calc convolutionKernelReal r j k l ^ 2 = _ := hkey
    _ ≤ ((4 : ℝ) ^ r *
        (periodicFrequencyWeight l ^ r + periodicFrequencyWeight (k - l) ^ r)) *
        (periodicFrequencyWeight l ^ (-r) * periodicFrequencyWeight (k - l) ^ (-r)) :=
      mul_le_mul_of_nonneg_right (h1.trans (weightR_peetre hr0 k l))
        (mul_nonneg (weightR_rpow_pos l _).le (weightR_rpow_pos (k - l) _).le)
    _ = (4 : ℝ) ^ r *
        ((periodicFrequencyWeight l ^ r * periodicFrequencyWeight l ^ (-r)) *
            periodicFrequencyWeight (k - l) ^ (-r) +
          (periodicFrequencyWeight (k - l) ^ r * periodicFrequencyWeight (k - l) ^ (-r)) *
            periodicFrequencyWeight l ^ (-r)) := by ring
    _ = _ := by rw [he l, he (k - l)]; ring

/-- The explicit squared scalar bound at order `r`:
`2 · 4^r · ∑_k W(k)^(-r)`. -/
def torusConvolutionBoundSquaredReal (r : ℝ) : ℝ :=
  2 * (4 : ℝ) ^ r * ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ (-r)

private lemma boundSquaredReal_nonneg (r : ℝ) : 0 ≤ torusConvolutionBoundSquaredReal r := by
  unfold torusConvolutionBoundSquaredReal
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (fun k ↦ (weightR_rpow_pos k _).le)

private lemma kernelReal_summable {r : ℝ} (hr : 3 ≤ r) (j : Fin 3) (k : PeriodicFrequency) :
    Summable (fun l ↦ convolutionKernelReal r j k l ^ 2) :=
  (((inverse_weightR_summable hr).add
    ((inverse_weightR_summable hr).comp_injective
      (sub_right_injective (b := k)))).mul_left ((4 : ℝ) ^ r)).of_nonneg_of_le
        (fun _ ↦ sq_nonneg _) (convolutionKernelReal_sq_le hr j k)

private lemma kernelReal_sum_le {r : ℝ} (hr : 3 ≤ r) (j : Fin 3) (k : PeriodicFrequency) :
    (∑' l, convolutionKernelReal r j k l ^ 2) ≤ torusConvolutionBoundSquaredReal r := by
  have h := (kernelReal_summable hr j k).tsum_le_tsum (convolutionKernelReal_sq_le hr j k)
    (((inverse_weightR_summable hr).add
      ((inverse_weightR_summable hr).comp_injective
        (sub_right_injective (b := k)))).mul_left ((4 : ℝ) ^ r))
  have hs : Summable (fun l ↦ periodicFrequencyWeight (k - l) ^ (-r)) :=
    (inverse_weightR_summable hr).comp_injective sub_right_injective
  rw [tsum_mul_left, (inverse_weightR_summable hr).tsum_add hs] at h
  rw [show (∑' l, periodicFrequencyWeight (k - l) ^ (-r)) =
    ∑' l, periodicFrequencyWeight l ^ (-r) from
    (Equiv.subLeft k).tsum_eq (fun l ↦ periodicFrequencyWeight l ^ (-r))] at h
  refine h.trans (le_of_eq ?_)
  unfold torusConvolutionBoundSquaredReal
  ring

/-! ## 3. Discrete Cauchy--Schwarz and the scalar estimate -/

private lemma scalar_energyR (a : PeriodicScalarData) :
    Summable (fun k ↦ ‖a k‖ ^ 2) ∧ (∑' k, ‖a k‖ ^ 2) = ‖a‖ ^ 2 := by
  constructor
  · simpa using (lp.memℓp a).summable (by norm_num)
  · simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a).symm

private lemma product_energyR (a b : PeriodicScalarData) :
    Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦ ‖a p.2‖ ^ 2 * ‖b (p.1 - p.2)‖ ^ 2) ∧
      (∑' k, ∑' l, ‖a l‖ ^ 2 * ‖b (k - l)‖ ^ 2) = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  let convolutionPairEquiv :
      (PeriodicFrequency × PeriodicFrequency) ≃ (PeriodicFrequency × PeriodicFrequency) :=
    { toFun := fun p ↦ (p.2, p.1 - p.2)
      invFun := fun p ↦ (p.1 + p.2, p.1)
      left_inv := fun p ↦ by ext <;> simp
      right_inv := fun p ↦ by ext <;> simp }
  have hp := (scalar_energyR a).1.mul_of_nonneg (scalar_energyR b).1
    (fun _ ↦ sq_nonneg _) (fun _ ↦ sq_nonneg _)
  have h : Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦
      ‖a p.2‖ ^ 2 * ‖b (p.1 - p.2)‖ ^ 2) :=
    hp.comp_injective (i := fun p : PeriodicFrequency × PeriodicFrequency ↦ (p.2, p.1 - p.2))
      convolutionPairEquiv.injective
  refine ⟨h, ?_⟩
  rw [← h.tsum_prod]
  change (∑' p, (fun q : PeriodicFrequency × PeriodicFrequency ↦
    ‖a q.1‖ ^ 2 * ‖b q.2‖ ^ 2) (convolutionPairEquiv p)) = _
  exact (convolutionPairEquiv.tsum_eq (fun q : PeriodicFrequency × PeriodicFrequency ↦
    ‖a q.1‖ ^ 2 * ‖b q.2‖ ^ 2)).trans (hp.tsum_prod.trans (by
      simp only [tsum_mul_left, tsum_mul_right, (scalar_energyR a).2, (scalar_energyR b).2]))

private lemma scalar_convolutionReal_norm_le {r : ℝ} (hr : 3 ≤ r) (a b : PeriodicScalarData)
    (j : Fin 3) (k : PeriodicFrequency) :
    ‖torusScalarConvectionReal r a b j k‖ ^ 2 ≤
      torusConvolutionBoundSquaredReal r * ∑' l, ‖a l‖ ^ 2 * ‖b (k - l)‖ ^ 2 := by
  let x : lp (fun _ : PeriodicFrequency ↦ ℝ) 2 :=
    ⟨fun l ↦ ‖a l‖ * ‖b (k - l)‖, memℓp_gen (by
      simpa [Real.norm_eq_abs, mul_pow] using (product_energyR a b).1.prod_factor k)⟩
  let w : lp (fun _ : PeriodicFrequency ↦ ℝ) 2 :=
    ⟨convolutionKernelReal r j k, memℓp_gen (by
      simpa [Real.norm_eq_abs] using kernelReal_summable hr j k)⟩
  have hh := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
      simpa using Real.HolderConjugate.two_two) w x
  have he (l : PeriodicFrequency) :
      ‖((periodicFrequencyWeight k ^ ((r - 1) / 2) : ℝ) : ℂ) * periodicDerivativeSymbol j k *
        (((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * a l *
          ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * b (k - l))‖ =
        ‖w l‖ * ‖x l‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simp only [abs_of_nonneg (weightR_rpow_pos k ((r - 1) / 2)).le,
      abs_of_nonneg (weightR_rpow_pos l (-r / 2)).le,
      abs_of_nonneg (weightR_rpow_pos (k - l) (-r / 2)).le]
    change _ = |convolutionKernelReal r j k l| * |‖a l‖ * ‖b (k - l)‖|
    rw [abs_of_nonneg (convolutionKernelReal_nonneg r j k l),
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    dsimp [convolutionKernelReal]
    ring
  have ht : ‖torusScalarConvectionReal r a b j k‖ ≤ ‖w‖ * ‖x‖ := by
    unfold torusScalarConvectionReal
    rw [← tsum_mul_left]
    have hs : Summable (fun l : PeriodicFrequency ↦
        ((periodicFrequencyWeight k ^ ((r - 1) / 2) : ℝ) : ℂ) * periodicDerivativeSymbol j k *
          (((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * a l *
            ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * b (k - l))) := by
      apply Summable.of_norm
      simpa only [he] using hh.1
    exact (norm_tsum_le_tsum_norm hs.norm).trans (by simpa only [he] using hh.2)
  have hw : ‖w‖ ^ 2 ≤ torusConvolutionBoundSquaredReal r := by
    rw [show ‖w‖ ^ 2 = ∑' l, convolutionKernelReal r j k l ^ 2 by
      simpa [w, Real.norm_eq_abs] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) w]
    exact kernelReal_sum_le hr j k
  have hx : ‖x‖ ^ 2 = ∑' l, ‖a l‖ ^ 2 * ‖b (k - l)‖ ^ 2 := by
    simpa [x, Real.norm_eq_abs, mul_pow] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  calc ‖torusScalarConvectionReal r a b j k‖ ^ 2 ≤ (‖w‖ * ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ = ‖w‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
    _ ≤ torusConvolutionBoundSquaredReal r * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = _ := by rw [hx]

/-- The complete scalar convolution belongs to `ℓ²` at every real order `r ≥ 3`. -/
theorem torusScalarConvectionReal_memℓp {r : ℝ} (hr : 3 ≤ r) (a b : PeriodicScalarData)
    (j : Fin 3) : Memℓp (torusScalarConvectionReal r a b j) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact ((product_energyR a b).1.prod.mul_left
    (torusConvolutionBoundSquaredReal r)).of_nonneg_of_le
      (fun _ ↦ sq_nonneg _) (scalar_convolutionReal_norm_le hr a b j)

/-- Scalar convolution on the actual complete coefficient carrier. -/
def torusScalarConvectionRealLp {r : ℝ} (hr : 3 ≤ r) (a b : PeriodicScalarData)
    (j : Fin 3) : PeriodicScalarData :=
  ⟨torusScalarConvectionReal r a b j, torusScalarConvectionReal_memℓp hr a b j⟩

/-- The uniform scalar bilinear estimate at real order `r ≥ 3`. -/
theorem torusScalarConvectionRealLp_norm_le {r : ℝ} (hr : 3 ≤ r) (a b : PeriodicScalarData)
    (j : Fin 3) :
    ‖torusScalarConvectionRealLp hr a b j‖ ≤
      Real.sqrt (torusConvolutionBoundSquaredReal r) * ‖a‖ * ‖b‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (by positivity)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have h := ((torusScalarConvectionReal_memℓp hr a b j).summable (by norm_num)).tsum_le_tsum
    (show ∀ k, ‖torusScalarConvectionReal r a b j k‖ ^ (2 : ℝ≥0∞).toReal ≤
      torusConvolutionBoundSquaredReal r * ∑' l, ‖a l‖ ^ 2 * ‖b (k - l)‖ ^ 2 by
      simpa using scalar_convolutionReal_norm_le hr a b j)
    ((product_energyR a b).1.prod.mul_left (torusConvolutionBoundSquaredReal r))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [tsum_mul_left, (product_energyR a b).2] at h
  simpa only [mul_pow, Real.sq_sqrt (boundSquaredReal_nonneg r),
    torusScalarConvectionRealLp, mul_assoc] using h

/-! ## 4. The vector symbol and the unprojected datum -/

/-- The real-order convection symbol: order-`r` inputs, order-`r-1` output. -/
def torusConvectionSymbolReal (r : ℝ) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  ((periodicFrequencyWeight k ^ ((r - 1) / 2) : ℝ) : ℂ) *
    ∑ j : Fin 3, periodicDerivativeSymbol j k *
      ∑' l : PeriodicFrequency,
        ((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * A.1 j l *
          ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * B.1 i (k - l)

/-- The Leray-projected real-order symbol, with the full zero-mode convention. -/
def torusProjectedConvectionSymbolReal (r : ℝ) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  if k = 0 then torusConvectionSymbolReal r A B i k else
    torusConvectionSymbolReal r A B i k -
      ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∑ j : Fin 3, (k j : ℂ) * torusConvectionSymbolReal r A B j k

/-- At order three the real-order vector symbol is lane 317's symbol. -/
theorem torusConvectionSymbolReal_three (A B : PeriodicSobolev 3) (i : Fin 3)
    (k : PeriodicFrequency) :
    torusConvectionSymbolReal 3 A B i k = torusConvectionSymbol A B i k := by
  unfold torusConvectionSymbolReal torusConvectionSymbol
  rw [show ((3 : ℝ) - 1) / 2 = 1 by norm_num, Real.rpow_one]

/-- At order three the projected real-order symbol is lane 317's projected symbol. -/
theorem torusProjectedConvectionSymbolReal_three (A B : PeriodicSobolev 3) (i : Fin 3)
    (k : PeriodicFrequency) :
    torusProjectedConvectionSymbolReal 3 A B i k = torusProjectedConvectionSymbol A B i k := by
  unfold torusProjectedConvectionSymbolReal torusProjectedConvectionSymbol
  simp only [torusConvectionSymbolReal_three]

private lemma convectionReal_eq_sum (r : ℝ) (A B : PeriodicSobolev r) (i : Fin 3)
    (k : PeriodicFrequency) :
    torusConvectionSymbolReal r A B i k =
      ∑ j : Fin 3, torusScalarConvectionReal r (A.1 j) (B.1 i) j k := by
  simp only [torusConvectionSymbolReal, torusScalarConvectionReal, Finset.mul_sum, mul_assoc]

private lemma convectionReal_real (r : ℝ) (A B : PeriodicSobolev r) (i : Fin 3)
    (k : PeriodicFrequency) :
    torusConvectionSymbolReal r A B i (-k) = star (torusConvectionSymbolReal r A B i k) := by
  have hc (j : Fin 3) :
      (∑' l : PeriodicFrequency,
        ((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * A.1 j l *
          ((periodicFrequencyWeight (-k - l) ^ (-r / 2) : ℝ) : ℂ) * B.1 i (-k - l)) =
      star (∑' l : PeriodicFrequency,
        ((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * A.1 j l *
          ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * B.1 i (k - l)) := by
    rw [← (Equiv.neg PeriodicFrequency).tsum_eq]
    simp only [Equiv.neg_apply, show ∀ l : PeriodicFrequency, -k - -l = -(k - l) by
      intro l; abel, torus_weight_neg]
    have hA : ∀ l, A.1 j (-l) = star (A.1 j l) := A.2 j
    have hB : ∀ l, B.1 i (-l) = star (B.1 i l) := B.2 i
    simp only [hA, hB, Complex.star_def]
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro l
    simp only [map_mul, Complex.conj_ofReal]
  unfold torusConvectionSymbolReal
  rw [torus_weight_neg]
  simp only [hc, Complex.star_def, map_mul, map_sum, Complex.conj_ofReal]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp [periodicDerivativeSymbol, map_mul, map_ofNat]

/-- The unprojected order-`(r-1)` convection datum. -/
def torusConvectionDatumReal {r : ℝ} (hr : 3 ≤ r) (A B : PeriodicSobolev r) :
    PeriodicSobolev (r - 1) :=
  ⟨WithLp.toLp 2 (fun i ↦ ∑ j : Fin 3, torusScalarConvectionRealLp hr (A.1 j) (B.1 i) j), by
    intro i k
    change (∑ j : Fin 3, torusScalarConvectionRealLp hr (A.1 j) (B.1 i) j) (-k) =
      star ((∑ j : Fin 3, torusScalarConvectionRealLp hr (A.1 j) (B.1 i) j) k)
    simpa only [lp.coeFn_sum, Finset.sum_apply, torusScalarConvectionRealLp,
      ← convectionReal_eq_sum] using convectionReal_real r A B i k⟩

theorem torusConvectionDatumReal_coeff {r : ℝ} (hr : 3 ≤ r) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvectionDatumReal hr A B).1 i k = torusConvectionSymbolReal r A B i k := by
  simp only [torusConvectionDatumReal, WithLp.ofLp_toLp, lp.coeFn_sum, Finset.sum_apply,
    torusScalarConvectionRealLp, convectionReal_eq_sum]

/-- The explicit uniform bilinear constant at real order `r`:
`9 · sqrt (2 · 4^r · ∑_k W(k)^(-r))`.  No optimality is claimed. -/
def torusConvolutionConstant_real (r : ℝ) : ℝ :=
  9 * Real.sqrt (torusConvolutionBoundSquaredReal r)

private lemma constantReal_nonneg (r : ℝ) : 0 ≤ torusConvolutionConstant_real r :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

-- Finite vector norms require elaboration of the nested lp/submodule carriers.
set_option maxHeartbeats 400000 in
theorem torusConvectionDatumReal_norm_le {r : ℝ} (hr : 3 ≤ r) (A B : PeriodicSobolev r) :
    ‖torusConvectionDatumReal hr A B‖ ≤ torusConvolutionConstant_real r * ‖A‖ * ‖B‖ := by
  let D := Real.sqrt (torusConvolutionBoundSquaredReal r) * ‖A‖ * ‖B‖
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg A)) (norm_nonneg B)
  have hi (i : Fin 3) : ‖(torusConvectionDatumReal hr A B).1 i‖ ≤ 3 * D := by
    change ‖∑ j : Fin 3, torusScalarConvectionRealLp hr (A.1 j) (B.1 i) j‖ ≤ _
    calc
      _ ≤ ∑ j : Fin 3, ‖torusScalarConvectionRealLp hr (A.1 j) (B.1 i) j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, D := by
        apply Finset.sum_le_sum
        intro j _
        apply (torusScalarConvectionRealLp_norm_le hr _ _ _).trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le A.1 j)
          (Real.sqrt_nonneg _)) (PiLp.norm_apply_le B.1 i) (norm_nonneg _) (by positivity)
      _ = 3 * D := by simp
  have hsq : ‖torusConvectionDatumReal hr A B‖ ^ 2 ≤ 3 * (3 * D) ^ 2 := by
    change ‖(torusConvectionDatumReal hr A B).1‖ ^ 2 ≤ _
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _i : Fin 3, (3 * D) ^ 2 :=
        Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hi i) 2)
      _ = _ := by simp
  change ‖torusConvectionDatumReal hr A B‖ ≤
    9 * Real.sqrt (torusConvolutionBoundSquaredReal r) * ‖A‖ * ‖B‖
  have he : 9 * Real.sqrt (torusConvolutionBoundSquaredReal r) * ‖A‖ * ‖B‖ = 9 * D := by
    dsimp only [D]; ring
  rw [he]
  nlinarith [norm_nonneg (torusConvectionDatumReal hr A B)]

/-! ## 5. Bilinearity, Leray projection and the bounded realization -/

private lemma convolutionReal_summable {r : ℝ} (hr : 0 ≤ r) (a b : PeriodicScalarData)
    (k : PeriodicFrequency) :
    Summable (fun l : PeriodicFrequency ↦
      ‖((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * a l *
        ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * b (k - l)‖) := by
  have hb (l : PeriodicFrequency) :
      ‖((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weightR_rpow_pos l _).le]
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_weightR l) (by linarith)
  have hA : Summable (fun l ↦ ‖a l‖ ^ 2) := (scalar_energyR a).1
  have hB : Summable (fun l ↦ ‖b (k - l)‖ ^ 2) :=
    (scalar_energyR b).1.comp_injective sub_right_injective
  apply (hA.add hB).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro l
  have hprod : ‖((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * a l *
      ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * b (k - l)‖ ≤
        ‖a l‖ * ‖b (k - l)‖ := by
    simp only [norm_mul]
    calc
      _ ≤ (1 * ‖a l‖) * 1 * ‖b (k - l)‖ := by gcongr <;> apply hb
      _ = _ := by ring
  exact hprod.trans (by nlinarith [sq_nonneg (‖a l‖ - ‖b (k - l)‖)])

private lemma convectionReal_add_left {r : ℝ} (hr : 0 ≤ r) (A D B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r (A + D) B i k =
      torusConvectionSymbolReal r A B i k + torusConvectionSymbolReal r D B i k := by
  unfold torusConvectionSymbolReal
  have h (j : Fin 3) := ((convolutionReal_summable hr (A.1 j) (B.1 i) k).of_norm).tsum_add
    ((convolutionReal_summable hr (D.1 j) (B.1 i) k).of_norm)
  simp only [Submodule.coe_add, PiLp.add_apply, lp.coeFn_add, Pi.add_apply,
    mul_add, add_mul, h, Finset.sum_add_distrib]

private lemma convectionReal_add_right {r : ℝ} (hr : 0 ≤ r) (A B D : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r A (B + D) i k =
      torusConvectionSymbolReal r A B i k + torusConvectionSymbolReal r A D i k := by
  unfold torusConvectionSymbolReal
  have h (j : Fin 3) := ((convolutionReal_summable hr (A.1 j) (B.1 i) k).of_norm).tsum_add
    ((convolutionReal_summable hr (A.1 j) (D.1 i) k).of_norm)
  simp only [Submodule.coe_add, PiLp.add_apply, lp.coeFn_add, Pi.add_apply,
    mul_add, h, Finset.sum_add_distrib]

private lemma convectionReal_smul_left (r c : ℝ) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r (c • A) B i k = (c : ℂ) * torusConvectionSymbolReal r A B i k := by
  unfold torusConvectionSymbolReal
  simp only [Submodule.coe_smul, PiLp.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.real_smul, mul_left_comm, mul_assoc, tsum_mul_left, Finset.mul_sum]

private lemma convectionReal_smul_right (r c : ℝ) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r A (c • B) i k = (c : ℂ) * torusConvectionSymbolReal r A B i k := by
  unfold torusConvectionSymbolReal
  simp only [Submodule.coe_smul, PiLp.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.real_smul, mul_left_comm, mul_assoc, tsum_mul_left, Finset.mul_sum]

/-- Leray projection of the unprojected real-order convolution datum. -/
def torusProjectedConvectionDatumReal {r : ℝ} (hr : 3 ≤ r) (A B : PeriodicSobolev r) :
    PeriodicSobolev (r - 1) :=
  Classical.choose (leray_exists_contraction (r - 1) (torusConvectionDatumReal hr A B))

theorem torusProjectedConvectionDatumReal_coeff {r : ℝ} (hr : 3 ≤ r) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    (torusProjectedConvectionDatumReal hr A B).1 i k =
      torusProjectedConvectionSymbolReal r A B i k := by
  have h := (Classical.choose_spec
    (leray_exists_contraction (r - 1) (torusConvectionDatumReal hr A B))).1 i k
  simpa only [torusProjectedConvectionDatumReal, periodicLeray,
    torusProjectedConvectionSymbolReal, torusConvectionDatumReal_coeff] using h

theorem torusProjectedConvectionDatumReal_norm_le {r : ℝ} (hr : 3 ≤ r)
    (A B : PeriodicSobolev r) :
    ‖torusProjectedConvectionDatumReal hr A B‖ ≤ torusConvolutionConstant_real r * ‖A‖ * ‖B‖ :=
  (Classical.choose_spec
    (leray_exists_contraction (r - 1) (torusConvectionDatumReal hr A B))).2.1.trans
      (torusConvectionDatumReal_norm_le hr A B)

private lemma datumR_ext {s : ℝ} {A B : PeriodicSobolev s}
    (h : ∀ i k, A.1 i k = B.1 i k) : A = B := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  exact lp.ext (funext (h i))

/-- The exact projected real-order convolution as a real bilinear map.

The output Sobolev index is a phantom label on the shared carrier, and it is
carried here as a separate parameter `t`: writing the nested bilinear type with
the literal index `r - 1` sends the elaborator into a `whnf` loop on real
subtraction while synthesizing `MulAction ℝ ↥(PeriodicSobolev (r - 1))`
(recorded in `research/T11/ATTEMPTS_CONVOLUTION_BOUND_REAL.md`).  The intended
instance is `t := r - 1`, taken in `torusConvolutionCLM_real` below; all
coefficient and norm statements are proved at the honest index `r - 1`. -/
def torusConvolutionLinearMapReal (r t : ℝ) (hr : 3 ≤ r) :
    PeriodicSobolev r →ₗ[ℝ] PeriodicSobolev r →ₗ[ℝ] PeriodicSobolev t :=
  LinearMap.mk₂ ℝ (torusProjectedConvectionDatumReal hr)
    (by
      intro A D B
      apply datumR_ext
      intro i k
      change (torusProjectedConvectionDatumReal hr (A + D) B).1 i k =
        (torusProjectedConvectionDatumReal hr A B).1 i k +
          (torusProjectedConvectionDatumReal hr D B).1 i k
      simp only [torusProjectedConvectionDatumReal_coeff, torusProjectedConvectionSymbolReal,
        convectionReal_add_left (by linarith : (0 : ℝ) ≤ r)]
      split_ifs <;> simp only [mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro c A B
      apply datumR_ext
      intro i k
      change (torusProjectedConvectionDatumReal hr (c • A) B).1 i k =
        (c : ℂ) * (torusProjectedConvectionDatumReal hr A B).1 i k
      simp only [torusProjectedConvectionDatumReal_coeff, torusProjectedConvectionSymbolReal,
        convectionReal_smul_left]
      split_ifs <;> simp only [Finset.mul_sum, mul_sub, mul_left_comm])
    (by
      intro A B D
      apply datumR_ext
      intro i k
      change (torusProjectedConvectionDatumReal hr A (B + D)).1 i k =
        (torusProjectedConvectionDatumReal hr A B).1 i k +
          (torusProjectedConvectionDatumReal hr A D).1 i k
      simp only [torusProjectedConvectionDatumReal_coeff, torusProjectedConvectionSymbolReal,
        convectionReal_add_right (by linarith : (0 : ℝ) ≤ r)]
      split_ifs <;> simp only [mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro c A B
      apply datumR_ext
      intro i k
      change (torusProjectedConvectionDatumReal hr A (c • B)).1 i k =
        (c : ℂ) * (torusProjectedConvectionDatumReal hr A B).1 i k
      simp only [torusProjectedConvectionDatumReal_coeff, torusProjectedConvectionSymbolReal,
        convectionReal_smul_right]
      split_ifs <;> simp only [Finset.mul_sum, mul_sub, mul_left_comm])

/-- Bounded real bilinear realization on the canonical carriers, with the output
order carried as the parameter `t`. -/
def torusConvolutionCLM_realAt (r t : ℝ) (hr : 3 ≤ r) :
    PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev t :=
  (torusConvolutionLinearMapReal r t hr).mkContinuous₂ (torusConvolutionConstant_real r)
    (torusProjectedConvectionDatumReal_norm_le hr)

/-- The map of this lane:
`torusConvolutionCLM_real r hr : PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev (r-1)`
for every real `r ≥ 3`.  The codomain index is pinned by the example below. -/
def torusConvolutionCLM_real (r : ℝ) (hr : 3 ≤ r) :=
  torusConvolutionCLM_realAt r (r - 1) hr

/-- The codomain of the lane's map is the order-`(r-1)` carrier. -/
example (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r) : PeriodicSobolev (r - 1) :=
  torusConvolutionCLM_real r hr A B

/-- Coefficient identity for the parametrized map. -/
theorem torusConvolutionCLM_realAt_coeff (r t : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_realAt r t hr A B).1 i k = torusProjectedConvectionSymbolReal r A B i k :=
  torusProjectedConvectionDatumReal_coeff hr A B i k

/-- The explicit operator-norm bound for the parametrized map. -/
theorem torusConvolutionCLM_realAt_norm_le (r t : ℝ) (hr : 3 ≤ r) :
    ‖torusConvolutionCLM_realAt r t hr‖ ≤ torusConvolutionConstant_real r := by
  apply LinearMap.mkContinuous₂_norm_le
  exact constantReal_nonneg r

/-- Coefficient identity: the map realizes the projected real-order symbol. -/
theorem torusConvolutionCLM_real_coeff (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_real r hr A B).1 i k = torusProjectedConvectionSymbolReal r A B i k :=
  torusProjectedConvectionDatumReal_coeff hr A B i k

/-- The explicit operator-norm bound. -/
theorem torusConvolutionCLM_real_norm_le (r : ℝ) (hr : 3 ≤ r) :
    ‖torusConvolutionCLM_real r hr‖ ≤ torusConvolutionConstant_real r :=
  torusConvolutionCLM_realAt_norm_le r (r - 1) hr

/-- The quadratic estimate in the usual applied form. -/
theorem torusConvolutionCLM_real_apply_norm_le (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r) :
    ‖torusConvolutionCLM_real r hr A B‖ ≤ torusConvolutionConstant_real r * ‖A‖ * ‖B‖ :=
  torusProjectedConvectionDatumReal_norm_le hr A B

/-! ## 6. Order transport and the identification with lane 317 -/

/-- Order transport is symmetric. -/
private lemma reweightR_symm {s t : ℝ} {A : PeriodicSobolev s} {B : PeriodicSobolev t}
    (h : IsPeriodicReweight s t A B) : IsPeriodicReweight t s B A := by
  intro i k
  rw [h i k, smul_smul, ← Real.rpow_add (weightR_pos k),
    show (s - t) / 2 + (t - s) / 2 = 0 by ring, Real.rpow_zero, one_smul]

/-- One summand of the convolution, after both inputs are reweighted. -/
private lemma reweight_pair (r r' : ℝ) (l m : PeriodicFrequency) (z u : ℂ) :
    ((periodicFrequencyWeight l ^ (-r' / 2) : ℝ) : ℂ) *
        ((periodicFrequencyWeight l ^ ((r' - r) / 2) : ℝ) • z) *
      ((periodicFrequencyWeight m ^ (-r' / 2) : ℝ) : ℂ) *
        ((periodicFrequencyWeight m ^ ((r' - r) / 2) : ℝ) • u)
      = ((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * z *
        ((periodicFrequencyWeight m ^ (-r / 2) : ℝ) : ℂ) * u := by
  have hkey (n : PeriodicFrequency) :
      ((periodicFrequencyWeight n ^ (-r' / 2) : ℝ) : ℂ) *
          ((periodicFrequencyWeight n ^ ((r' - r) / 2) : ℝ) : ℂ)
        = ((periodicFrequencyWeight n ^ (-r / 2) : ℝ) : ℂ) := by
    rw [ofReal_weightR_mul, show -r' / 2 + (r' - r) / 2 = -r / 2 by ring]
  rw [Complex.real_smul, Complex.real_smul]
  calc _ = (((periodicFrequencyWeight l ^ (-r' / 2) : ℝ) : ℂ) *
        ((periodicFrequencyWeight l ^ ((r' - r) / 2) : ℝ) : ℂ)) * z *
      ((((periodicFrequencyWeight m ^ (-r' / 2) : ℝ) : ℂ) *
        ((periodicFrequencyWeight m ^ ((r' - r) / 2) : ℝ) : ℂ)) * u) := by ring
    _ = _ := by rw [hkey l, hkey m]; ring

/-- Order transport of the unprojected symbol: the order-`r'` symbol on
reweighted data is the order-`r` symbol multiplied by `W(k)^((r'-r)/2)`. -/
theorem torusConvectionSymbolReal_reweight (r r' : ℝ) {A B : PeriodicSobolev r}
    {A' B' : PeriodicSobolev r'} (hA : IsPeriodicReweight r r' A A')
    (hB : IsPeriodicReweight r r' B B') (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r' A' B' i k =
      ((periodicFrequencyWeight k ^ ((r' - r) / 2) : ℝ) : ℂ) *
        torusConvectionSymbolReal r A B i k := by
  have hT (j : Fin 3) :
      (∑' l : PeriodicFrequency,
        ((periodicFrequencyWeight l ^ (-r' / 2) : ℝ) : ℂ) * A'.1 j l *
          ((periodicFrequencyWeight (k - l) ^ (-r' / 2) : ℝ) : ℂ) * B'.1 i (k - l)) =
      ∑' l : PeriodicFrequency,
        ((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * A.1 j l *
          ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * B.1 i (k - l) := by
    apply tsum_congr
    intro l
    rw [hA j l, hB i (k - l)]
    exact reweight_pair r r' l (k - l) (A.1 j l) (B.1 i (k - l))
  unfold torusConvectionSymbolReal
  rw [show (r' - 1) / 2 = (r' - r) / 2 + (r - 1) / 2 by ring, ← ofReal_weightR_mul, mul_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hT j]

/-- Order transport of the projected symbol: the Leray formula is `ℂ`-linear at
each frequency, so it commutes with the weight transport. -/
theorem torusProjectedConvectionSymbolReal_reweight (r r' : ℝ) {A B : PeriodicSobolev r}
    {A' B' : PeriodicSobolev r'} (hA : IsPeriodicReweight r r' A A')
    (hB : IsPeriodicReweight r r' B B') (i : Fin 3) (k : PeriodicFrequency) :
    torusProjectedConvectionSymbolReal r' A' B' i k =
      ((periodicFrequencyWeight k ^ ((r' - r) / 2) : ℝ) : ℂ) *
        torusProjectedConvectionSymbolReal r A B i k := by
  have hsum : (∑ j : Fin 3, (k j : ℂ) * torusConvectionSymbolReal r' A' B' j k) =
      ((periodicFrequencyWeight k ^ ((r' - r) / 2) : ℝ) : ℂ) *
        ∑ j : Fin 3, (k j : ℂ) * torusConvectionSymbolReal r A B j k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [torusConvectionSymbolReal_reweight r r' hA hB j k]
    ring
  unfold torusProjectedConvectionSymbolReal
  split_ifs with hk
  · exact torusConvectionSymbolReal_reweight r r' hA hB i k
  · rw [torusConvectionSymbolReal_reweight r r' hA hB i k, hsum]
    ring

/-- The reweighting-compatibility statement for the bounded maps: transporting
both inputs from order `r` to order `r'` transports the value from order `r-1`
to order `r'-1`.  The brief's hypothesis `r ≤ r'` is not needed. -/
theorem torusConvolutionCLM_real_reweight (r r' : ℝ) (hr : 3 ≤ r) (hr' : 3 ≤ r')
    {A B : PeriodicSobolev r} {A' B' : PeriodicSobolev r'}
    (hA : IsPeriodicReweight r r' A A') (hB : IsPeriodicReweight r r' B B') :
    IsPeriodicReweight (r - 1) (r' - 1)
      (torusConvolutionCLM_real r hr A B) (torusConvolutionCLM_real r' hr' A' B') := by
  intro i k
  rw [torusConvolutionCLM_real_coeff, torusConvolutionCLM_real_coeff,
    torusProjectedConvectionSymbolReal_reweight r r' hA hB i k, Complex.real_smul,
    show (r' - 1 - (r - 1)) / 2 = (r' - r) / 2 by ring]

/-- The coefficient identity in the `.1 i k` form asked for by the lane: the
order-`r` map is lane 317's projected convection symbol of the order-three
reweighted data, transported back by the weight `W(k)^((r-3)/2)`. -/
theorem torusConvolutionCLM_real_coeff_transport (r : ℝ) (hr : 3 ≤ r)
    (A B : PeriodicSobolev r) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_real r hr A B).1 i k =
      ((periodicFrequencyWeight k ^ ((r - 3) / 2) : ℝ) : ℂ) *
        torusProjectedConvectionSymbol
          (persistenceDown r 3 hr A) (persistenceDown r 3 hr B) i k := by
  have hA : IsPeriodicReweight 3 r (persistenceDown r 3 hr A) A :=
    reweightR_symm (persistenceDown_reweight r 3 hr A)
  have hB : IsPeriodicReweight 3 r (persistenceDown r 3 hr B) B :=
    reweightR_symm (persistenceDown_reweight r 3 hr B)
  rw [torusConvolutionCLM_real_coeff,
    torusProjectedConvectionSymbolReal_reweight 3 r hA hB i k,
    torusProjectedConvectionSymbolReal_three]

/-- At order three the new map has lane 317's coefficients. -/
theorem torusConvolutionCLM_real_coeff_three (A B : PeriodicSobolev 3) (i : Fin 3)
    (k : PeriodicFrequency) :
    (torusConvolutionCLM_real 3 le_rfl A B).1 i k = torusProjectedConvectionSymbol A B i k := by
  rw [torusConvolutionCLM_real_coeff, torusProjectedConvectionSymbolReal_three]

/-! ## 7. Non-vacuity on constant modes -/

theorem torusConvectionSymbolReal_constants (r : ℝ)
    (c d : NavierStokes.ProblemStatement.Space) (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r (torusConstantDatum r c) (torusConstantDatum r d) i k = 0 := by
  by_cases hk : k = 0
  · subst k
    simp [torusConvectionSymbolReal, periodicDerivativeSymbol]
  · have hz (j : Fin 3) (l : PeriodicFrequency) :
        ((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) *
          (torusConstantDatum r c).1 j l *
          ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) *
          (torusConstantDatum r d).1 i (k - l) = 0 := by
      by_cases hl : l = 0
      · subst l
        simp [torusConstantDatum, lp.single_apply, hk]
      · simp [torusConstantDatum, lp.single_apply, hl]
    simp [torusConvectionSymbolReal, hz]

theorem torusProjectedConvectionSymbolReal_constants (r : ℝ)
    (c d : NavierStokes.ProblemStatement.Space) (i : Fin 3) (k : PeriodicFrequency) :
    torusProjectedConvectionSymbolReal r (torusConstantDatum r c) (torusConstantDatum r d) i k
      = 0 := by
  simp [torusProjectedConvectionSymbolReal, torusConvectionSymbolReal_constants]

/-- Two constant-mode data test the actual real-order convolution map. -/
theorem torusConvolutionCLM_real_constants (r : ℝ) (hr : 3 ≤ r)
    (c d : NavierStokes.ProblemStatement.Space) :
    torusConvolutionCLM_real r hr (torusConstantDatum r c) (torusConstantDatum r d) = 0 := by
  apply datumR_ext
  intro i k
  rw [torusConvolutionCLM_real_coeff, torusProjectedConvectionSymbolReal_constants]
  rfl

/-- The real-order construction re-discharges lane 313's residual convolution
input at order three, with the same coefficients as lane 317. -/
theorem torusConvolutionInput_ofReal : TorusConvolutionInput :=
  ⟨torusConvolutionCLM_realAt 3 2 le_rfl, fun A B i k ↦ by
    rw [torusConvolutionCLM_realAt_coeff, torusProjectedConvectionSymbolReal_three]⟩

example : ∃ A B : PeriodicSobolev (7 / 2 : ℝ),
    A ≠ 0 ∧ B ≠ 0 ∧
      torusConvolutionCLM_real (7 / 2 : ℝ) (by norm_num) A B = 0 := by
  let c : NavierStokes.ProblemStatement.Space := WithLp.toLp 2 (fun _ ↦ 1)
  let A := torusConstantDatum (7 / 2 : ℝ) c
  have hA : A ≠ 0 := by
    intro h
    have hc := congrArg
      (fun D : PeriodicSobolev (7 / 2 : ℝ) ↦ D.1 (0 : Fin 3) (0 : PeriodicFrequency)) h
    change (1 : ℂ) = 0 at hc
    exact one_ne_zero hc
  exact ⟨A, A, hA, hA, torusConvolutionCLM_real_constants (7 / 2 : ℝ) (by norm_num) c c⟩

end NSFormalization.Section3.T11
