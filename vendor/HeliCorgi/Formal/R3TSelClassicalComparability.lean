import Formal.R3TSelBridge
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.Order.Chebyshev

/-!
# SEL-1 discharged: classical Sobolev comparability on the Schwartz core

This file proves the open T-SEL bridge statement `R3TSelClassicalSobolevComparability`
(`Formal/R3TSelBridge.lean`): there are explicit positive constants `c₁, c₂` such that
for every Schwartz velocity field `φ`,

`c₁ ‖J³φ‖²_{L²} ≤ ∑_{n ≤ 3} ‖D^n φ‖²_{L²} ≤ c₂ ‖J³φ‖²_{L²}`,

where `D^n φ = iteratedFDeriv ℝ n φ` carries the operator norm and `‖J³φ‖` is the
carrier norm of the canonical order-three Bessel coordinate `r3SchwartzToHsCLM 3 φ`.

Proof route (all on the Schwartz core, no distribution theory):

1. **Direction tuples.**  For a tuple `v : Fin n → Fin 3` the iterated line derivative
   `∂^{e ∘ v} φ` is again Schwartz (`LineDeriv.iteratedLineDerivOpCLM`), and pointwise
   equals the iterated Fréchet derivative applied to the basis tuple
   (`iteratedLineDerivOp_eq_iteratedFDeriv`).
2. **Fourier side.**  By iterating `SchwartzMap.fourier_lineDerivOp_eq`,
   `‖𝓕(∂^{m}φ)(ξ)‖ = ∏ᵢ (2π |⟪ξ, mᵢ⟫|) · ‖𝓕φ(ξ)‖`; Plancherel for Schwartz functions
   (`SchwartzMap.integral_norm_sq_fourier`) turns each tuple's squared `L²` norm into
   the frequency integral with weight `(2π)^{2n} ∏ᵢ ξ_{vᵢ}²`.
3. **Tuple sum.**  `Fintype.sum_pow` gives `∑_v ∏ᵢ ξ_{vᵢ}² = ‖ξ‖^{2n}`, so the tuple-sum
   energy at order `n` is exactly `(2π)^{2n} ∫ ‖ξ‖^{2n} ‖𝓕φ‖²`.
4. **Operator norm vs tuples.**  Pointwise, `‖A(e∘v)‖ ≤ ‖A‖` and (multilinear basis
   expansion) `‖A‖ ≤ ∑_v ‖A(e∘v)‖`, so with Cauchy–Schwarz the squared operator-norm
   energies and the tuple-sum energies agree up to the dimension factor `3ⁿ ≤ 27`.
5. **Weight comparison.**  Pointwise
   `(1/3)(1+‖ξ‖²)³ ≤ ∑_{n ≤ 3} (2π)^{2n}‖ξ‖^{2n} ≤ (4π²)³(1+‖ξ‖²)³` (using `π ≥ 1`),
   and `∫ (1+‖ξ‖²)³ ‖𝓕φ‖² = ‖r3SchwartzToHsCLM 3 φ‖²` by the repository's explicit
   frequency description of the Bessel coordinate.

The resulting explicit constants are `c₁ = 1/81` and `c₂ = 27 (4π²)³`.  Only the
existence of positive constants is consumed downstream; no sharpness is claimed.
-/

namespace MNS2

open MeasureTheory SchwartzMap LineDeriv Real
open scoped FourierTransform SchwartzMap ENNReal NNReal ContDiff

noncomputable section

/-! ## Generic helper: squared `toReal` of the `L²` seminorm as an integral -/

/-- For an `L²` function into any normed group, the squared real-valued `L²` seminorm is
the integral of the squared norm. -/
theorem sq_toReal_eLpNorm_two {E : Type*} [NormedAddCommGroup E] {f : R3 → E}
    (hf : MemLp f 2 (volume : Measure R3)) :
    ((eLpNorm f 2 volume).toReal) ^ 2 = ∫ x : R3, ‖f x‖ ^ 2 := by
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have hcong : (∫ x : R3, ‖f x‖ ^ ((2 : ℝ≥0∞).toReal)) = ∫ x : R3, ‖f x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖f x‖ ^ ((2 : ℝ≥0∞).toReal) = ‖f x‖ ^ (2 : ℕ)
    rw [h2, ← Real.rpow_natCast ‖f x‖ 2]
    norm_num
  have hint : (0 : ℝ) ≤ ∫ x : R3, ‖f x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, hcong, h2,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hint _),
    ← Real.rpow_natCast ((∫ x : R3, ‖f x‖ ^ 2) ^ ((2 : ℝ)⁻¹)) 2,
    ← Real.rpow_mul hint]
  norm_num

/-! ## The direction-tuple derivatives -/

/-- The standard-basis direction tuple attached to an index tuple. -/
def r3TSelTupleDirections {n : ℕ} (v : Fin n → Fin 3) : Fin n → R3 :=
  fun i => r3StdBasis (v i)

/-- The iterated line derivative of a Schwartz velocity along a direction tuple is
pointwise the iterated Fréchet derivative applied to that tuple. -/
theorem r3TSel_iteratedLineDerivOp_eq (n : ℕ) (v : Fin n → Fin 3)
    (φ : R3SchwartzVelocity) (x : R3) :
    (∂^{r3TSelTupleDirections v} φ) x =
      iteratedFDeriv ℝ n (⇑φ) x (r3TSelTupleDirections v) :=
  SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv

/-! ## Fourier transform of iterated line derivatives -/

/-- Iterating `SchwartzMap.fourier_lineDerivOp_eq`: the Fourier transform of an `n`-fold
line derivative has pointwise norm `∏ᵢ (2π |⟪ξ, mᵢ⟫|)` times that of the transform. -/
theorem norm_fourier_iteratedLineDerivOp (n : ℕ) (m : Fin n → R3)
    (ψ : R3SchwartzVelocity) (ξ : R3) :
    ‖(𝓕 (∂^{m} ψ) : R3SchwartzVelocity) ξ‖ =
      (∏ i, (2 * π * |inner ℝ ξ (m i)|)) * ‖(𝓕 ψ : R3SchwartzVelocity) ξ‖ := by
  induction n generalizing ψ with
  | zero => simp
  | succ n ih =>
    have hsucc : ∂^{m} ψ = ∂_{m 0} (∂^{Fin.tail m} ψ) :=
      iteratedLineDerivOp_succ_left m ψ
    have hgrowth : (Function.HasTemperateGrowth (inner ℝ · (m 0))) :=
      ((innerSL ℝ).flip (m 0)).hasTemperateGrowth
    have hnorm2pi : ‖(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
      simp [Complex.norm_I, abs_of_nonneg pi_nonneg]
    have hstep : ‖(𝓕 (∂^{m} ψ) : R3SchwartzVelocity) ξ‖ =
        (2 * π * |inner ℝ ξ (m 0)|) *
          ‖(𝓕 (∂^{Fin.tail m} ψ) : R3SchwartzVelocity) ξ‖ := by
      rw [hsucc, SchwartzMap.fourier_lineDerivOp_eq]
      rw [show ((2 * ↑π * Complex.I) •
          SchwartzMap.smulLeftCLM R3C (inner ℝ · (m 0)) (𝓕 (∂^{Fin.tail m} ψ)) :
            R3SchwartzVelocity) ξ =
          (2 * ↑π * Complex.I) •
            (SchwartzMap.smulLeftCLM R3C (inner ℝ · (m 0)) (𝓕 (∂^{Fin.tail m} ψ)) ξ) from
        rfl]
      rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth, norm_smul, norm_smul, hnorm2pi,
        Real.norm_eq_abs]
      ring
    rw [hstep, ih (Fin.tail m)]
    have htailprod : (∏ i : Fin n, (2 * π * |inner ℝ ξ (Fin.tail m i)|)) =
        ∏ i : Fin n, (2 * π * |inner ℝ ξ (m i.succ)|) := rfl
    rw [htailprod, Fin.prod_univ_succ]
    ring

/-! ## Per-tuple Plancherel: the tuple energy as a frequency integral -/

/-- The frequency weight of one direction tuple. -/
theorem norm_fourier_tuple_deriv (n : ℕ) (v : Fin n → Fin 3)
    (φ : R3SchwartzVelocity) (ξ : R3) :
    ‖(𝓕 (∂^{r3TSelTupleDirections v} φ) : R3SchwartzVelocity) ξ‖ ^ 2 =
      (2 * π) ^ (2 * n) * (∏ i, (ξ (v i)) ^ 2) *
        ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by
  rw [norm_fourier_iteratedLineDerivOp]
  have hinner : ∀ i, inner ℝ ξ (r3TSelTupleDirections v i) = ξ (v i) := fun i =>
    inner_r3StdBasis ξ (v i)
  rw [mul_pow]
  congr 1
  calc (∏ i, 2 * π * |inner ℝ ξ (r3TSelTupleDirections v i)|) ^ 2
      = ∏ i, (2 * π * |ξ (v i)|) ^ 2 := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hinner i]
    _ = ∏ i, ((2 * π) ^ 2 * (ξ (v i)) ^ 2) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [mul_pow, sq_abs]
    _ = (2 * π) ^ (2 * n) * ∏ i, (ξ (v i)) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← pow_mul]

/-- The Fourier data of a Schwartz velocity is pointwise bounded. -/
theorem exists_bound_fourier (φ : R3SchwartzVelocity) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : R3, ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := (𝓕 φ : R3SchwartzVelocity).decay 0 0
  refine ⟨C, hCpos.le, fun ξ => ?_⟩
  have := hC ξ
  simpa using this

/-- The weighted frequency energies are integrable. -/
theorem integrable_pow_mul_norm_sq_fourier (φ : R3SchwartzVelocity) (k : ℕ) :
    Integrable (fun ξ : R3 => ‖ξ‖ ^ k * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) volume := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_fourier φ
  have hint : Integrable
      (fun ξ : R3 => ‖ξ‖ ^ k * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖) volume :=
    (𝓕 φ : R3SchwartzVelocity).integrable_pow_mul volume k
  refine (hint.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (((continuous_norm.pow k).mul
      (((𝓕 φ : R3SchwartzVelocity).continuous).norm.pow 2))).aestronglyMeasurable
  · have h1 : ‖ξ‖ ^ k * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 =
        (‖ξ‖ ^ k * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖) *
          ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ := by ring
    have h2 : (0 : ℝ) ≤ ‖ξ‖ ^ k * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), h1]
    calc (‖ξ‖ ^ k * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖
        ≤ (‖ξ‖ ^ k * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖) * C := by
          exact mul_le_mul_of_nonneg_left (hC ξ) h2
      _ = C * (‖ξ‖ ^ k * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖) := by ring

/-- Each single-tuple frequency energy integrand is integrable. -/
theorem integrable_tuple_weight (n : ℕ) (v : Fin n → Fin 3) (φ : R3SchwartzVelocity) :
    Integrable (fun ξ : R3 =>
      (∏ i, (ξ (v i)) ^ 2) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) volume := by
  refine (integrable_pow_mul_norm_sq_fourier φ (2 * n)).mono'
    ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have hcoord : ∀ i : Fin n, Continuous fun ξ : R3 => (ξ (v i)) ^ 2 := fun i =>
      ((EuclideanSpace.proj (v i) : R3 →L[ℝ] ℝ).continuous).pow 2
    exact (continuous_finsetProd _ fun i _ => hcoord i).mul
      (((𝓕 φ : R3SchwartzVelocity).continuous).norm.pow 2)
  · have hprod : (∏ i, (ξ (v i)) ^ 2) ≤ ‖ξ‖ ^ (2 * n) := by
      have h1 : ∀ i : Fin n, (ξ (v i)) ^ 2 ≤ ‖ξ‖ ^ 2 := fun i => by
        have h2 : |ξ (v i)| ≤ ‖ξ‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ (v i)
        calc (ξ (v i)) ^ 2 = |ξ (v i)| ^ 2 := (sq_abs _).symm
          _ ≤ ‖ξ‖ ^ 2 := by nlinarith [abs_nonneg (ξ (v i))]
      calc (∏ i, (ξ (v i)) ^ 2) ≤ ∏ _i : Fin n, ‖ξ‖ ^ 2 :=
            Finset.prod_le_prod (fun i _ => sq_nonneg _) (fun i _ => h1 i)
        _ = ‖ξ‖ ^ (2 * n) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    have hprod0 : (0 : ℝ) ≤ ∏ i, (ξ (v i)) ^ 2 :=
      Finset.prod_nonneg fun i _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod0 (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hprod (sq_nonneg _)

/-- **Per-tuple Plancherel**: the physical `L²` energy of one direction-tuple derivative
is its weighted frequency energy. -/
theorem integral_norm_sq_tuple_deriv (n : ℕ) (v : Fin n → Fin 3)
    (φ : R3SchwartzVelocity) :
    (∫ x : R3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2) =
      (2 * π) ^ (2 * n) * ∫ ξ : R3,
        (∏ i, (ξ (v i)) ^ 2) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier (∂^{r3TSelTupleDirections v} φ)]
  rw [show (∫ ξ : R3, ‖(𝓕 (∂^{r3TSelTupleDirections v} φ) : R3SchwartzVelocity) ξ‖ ^ 2) =
      ∫ ξ : R3, (2 * π) ^ (2 * n) * ((∏ i, (ξ (v i)) ^ 2) *
        ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) from
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
      show ‖(𝓕 (∂^{r3TSelTupleDirections v} φ) : R3SchwartzVelocity) ξ‖ ^ 2 =
        (2 * π) ^ (2 * n) * ((∏ i, (ξ (v i)) ^ 2) *
          ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2)
      rw [norm_fourier_tuple_deriv, mul_assoc])]
  rw [integral_const_mul]

/-! ## The tuple-sum energy at order `n` -/

/-- The tuple-sum energy at order `n`, as a closed frequency integral:
`∑_v ∫ ‖∂^{v}φ‖² = (2π)^{2n} ∫ ‖ξ‖^{2n} ‖𝓕φ‖²`. -/
theorem sum_tuple_energies (n : ℕ) (φ : R3SchwartzVelocity) :
    (∑ v : Fin n → Fin 3, ∫ x : R3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2) =
      (2 * π) ^ (2 * n) *
        ∫ ξ : R3, ‖ξ‖ ^ (2 * n) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by
  have h1 : (∑ v : Fin n → Fin 3, ∫ x : R3,
      ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2) =
      (2 * π) ^ (2 * n) * ∑ v : Fin n → Fin 3, ∫ ξ : R3,
        (∏ i, (ξ (v i)) ^ 2) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => integral_norm_sq_tuple_deriv n v φ
  rw [h1]
  congr 1
  rw [← integral_finsetSum _ (fun v _ => integrable_tuple_weight n v φ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (∑ v : Fin n → Fin 3, (∏ i, (ξ (v i)) ^ 2) *
      ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) =
    ‖ξ‖ ^ (2 * n) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2
  rw [← Finset.sum_mul]
  congr 1
  have hnorm : ‖ξ‖ ^ (2 * n) = (∑ c : Fin 3, (ξ c) ^ 2) ^ n := by
    have hsq : ‖ξ‖ ^ 2 = ∑ c : Fin 3, (ξ c) ^ 2 := by
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)]
      exact Finset.sum_congr rfl fun c _ => by rw [Real.norm_eq_abs, sq_abs]
    rw [pow_mul, hsq]
  rw [hnorm, Fintype.sum_pow]

/-! ## Operator norm versus direction tuples, pointwise -/

/-- Expansion of a Euclidean vector in the standard basis. -/
theorem r3_eq_sum_stdBasis (y : R3) : y = ∑ c : Fin 3, y c • r3StdBasis c := by
  ext j
  rw [show (∑ c : Fin 3, y c • r3StdBasis c) j = ∑ c : Fin 3, y c • (r3StdBasis c j) from
    by simp]
  unfold r3StdBasis
  simp [PiLp.single_apply]

/-- Pointwise basis-expansion bound: the operator norm of a continuous multilinear map on
`R3` is at most the sum of its values on standard-basis tuples. -/
theorem multilinear_norm_le_sum_tuples {n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) R3C) :
    ‖A‖ ≤ ∑ v : Fin n → Fin 3, ‖A (r3TSelTupleDirections v)‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun v _ => norm_nonneg _) (fun m => ?_)
  have hexp : A m = ∑ v : Fin n → Fin 3,
      (∏ i, m i (v i)) • A (r3TSelTupleDirections v) := by
    have hm : m = fun i => ∑ c : Fin 3, m i c • r3StdBasis c := by
      funext i
      exact r3_eq_sum_stdBasis (m i)
    calc A m = A (fun i => ∑ c : Fin 3, m i c • r3StdBasis c) := by rw [← hm]
      _ = ∑ v : Fin n → Fin 3, A (fun i => m i (v i) • r3StdBasis (v i)) :=
          A.map_sum (fun i c => m i c • r3StdBasis c)
      _ = ∑ v : Fin n → Fin 3, (∏ i, m i (v i)) • A (r3TSelTupleDirections v) :=
          Finset.sum_congr rfl fun v _ => A.map_smul_univ _ _
  rw [hexp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [norm_smul]
  have hcoef : ‖∏ i, m i (v i)‖ ≤ ∏ i, ‖m i‖ := by
    rw [Real.norm_eq_abs, Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (m i) (v i)
  calc ‖∏ i, m i (v i)‖ * ‖A (r3TSelTupleDirections v)‖
      ≤ (∏ i, ‖m i‖) * ‖A (r3TSelTupleDirections v)‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ = ‖A (r3TSelTupleDirections v)‖ * ∏ i, ‖m i‖ := by ring

/-- Each standard-basis tuple value is dominated by the operator norm. -/
theorem norm_tuple_le_multilinear_norm {n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => R3) R3C) (v : Fin n → Fin 3) :
    ‖A (r3TSelTupleDirections v)‖ ≤ ‖A‖ := by
  refine (A.le_opNorm _).trans ?_
  have hone : (∏ i, ‖r3TSelTupleDirections v i‖) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    unfold r3TSelTupleDirections r3StdBasis
    simp [PiLp.norm_single]
  rw [hone, mul_one]

/-! ## Integrability and the order-`n` comparison -/

/-- The iterated Fréchet derivative of a Schwartz velocity is square integrable. -/
theorem memLp_two_iteratedFDeriv (n : ℕ) (φ : R3SchwartzVelocity) :
    MemLp (iteratedFDeriv ℝ n (⇑φ)) 2 (volume : Measure R3) := by
  have hcont : Continuous (iteratedFDeriv ℝ n (⇑φ)) :=
    (φ.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hdom : MemLp (fun x : R3 => ∑ v : Fin n → Fin 3,
      ‖(∂^{r3TSelTupleDirections v} φ) x‖) 2 (volume : Measure R3) := by
    refine memLp_finsetSum Finset.univ fun v _ => ?_
    exact ((∂^{r3TSelTupleDirections v} φ).memLp 2).norm
  refine MemLp.of_le hdom hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h1 := multilinear_norm_le_sum_tuples (iteratedFDeriv ℝ n (⇑φ) x)
  have h2 : ∀ v : Fin n → Fin 3,
      ‖iteratedFDeriv ℝ n (⇑φ) x (r3TSelTupleDirections v)‖ =
        ‖(∂^{r3TSelTupleDirections v} φ) x‖ := fun v => by
    rw [r3TSel_iteratedLineDerivOp_eq]
  calc ‖iteratedFDeriv ℝ n (⇑φ) x‖
      ≤ ∑ v : Fin n → Fin 3, ‖iteratedFDeriv ℝ n (⇑φ) x (r3TSelTupleDirections v)‖ := h1
    _ = ∑ v : Fin n → Fin 3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ :=
        Finset.sum_congr rfl fun v _ => h2 v
    _ ≤ ‖∑ v : Fin n → Fin 3, ‖(∂^{r3TSelTupleDirections v} φ) x‖‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _

/-- The order-`n` squared operator-norm energy. -/
def r3TSelOpEnergy (n : ℕ) (φ : R3SchwartzVelocity) : ℝ :=
  ∫ x : R3, ‖iteratedFDeriv ℝ n (⇑φ) x‖ ^ 2

/-- The order-`n` tuple-sum energy. -/
def r3TSelTupleEnergy (n : ℕ) (φ : R3SchwartzVelocity) : ℝ :=
  ∑ v : Fin n → Fin 3, ∫ x : R3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2

theorem r3TSelOpEnergy_nonneg (n : ℕ) (φ : R3SchwartzVelocity) :
    0 ≤ r3TSelOpEnergy n φ :=
  integral_nonneg fun _x => sq_nonneg _

/-- The squared operator-norm energy integrand is integrable. -/
theorem integrable_opEnergy (n : ℕ) (φ : R3SchwartzVelocity) :
    Integrable (fun x : R3 => ‖iteratedFDeriv ℝ n (⇑φ) x‖ ^ 2) volume := by
  have h := (memLp_two_iteratedFDeriv n φ).norm
  exact (memLp_two_iff_integrable_sq
    ((memLp_two_iteratedFDeriv n φ).aestronglyMeasurable.norm)).mp h

/-- The squared tuple-derivative integrand is integrable. -/
theorem integrable_tuple_sq (n : ℕ) (v : Fin n → Fin 3) (φ : R3SchwartzVelocity) :
    Integrable (fun x : R3 => ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2) volume := by
  have h := ((∂^{r3TSelTupleDirections v} φ).memLp 2
    (μ := (volume : Measure R3))).norm
  exact (memLp_two_iff_integrable_sq
    ((∂^{r3TSelTupleDirections v} φ).continuous.aestronglyMeasurable.norm)).mp h

/-- Order-`n` comparison, upper half: the operator-norm energy is at most `3ⁿ` times the
tuple-sum energy. -/
theorem opEnergy_le_tupleEnergy (n : ℕ) (φ : R3SchwartzVelocity) :
    r3TSelOpEnergy n φ ≤ 3 ^ n * r3TSelTupleEnergy n φ := by
  unfold r3TSelOpEnergy r3TSelTupleEnergy
  have hsum : ∀ x : R3, ‖iteratedFDeriv ℝ n (⇑φ) x‖ ^ 2 ≤
      3 ^ n * ∑ v : Fin n → Fin 3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2 := by
    intro x
    have h1 : ‖iteratedFDeriv ℝ n (⇑φ) x‖ ≤
        ∑ v : Fin n → Fin 3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ := by
      refine (multilinear_norm_le_sum_tuples _).trans_eq ?_
      exact Finset.sum_congr rfl fun v _ => by rw [r3TSel_iteratedLineDerivOp_eq]
    have h2 : ‖iteratedFDeriv ℝ n (⇑φ) x‖ ^ 2 ≤
        (∑ v : Fin n → Fin 3, ‖(∂^{r3TSelTupleDirections v} φ) x‖) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ n (⇑φ) x‖ := norm_nonneg _
      nlinarith [Finset.sum_nonneg
        (fun (v : Fin n → Fin 3) (_ : v ∈ Finset.univ) =>
          norm_nonneg ((∂^{r3TSelTupleDirections v} φ) x))]
    refine h2.trans ?_
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n → Fin 3)))
      (f := fun v => ‖(∂^{r3TSelTupleDirections v} φ) x‖)
    calc (∑ v : Fin n → Fin 3, ‖(∂^{r3TSelTupleDirections v} φ) x‖) ^ 2
        ≤ (Finset.univ.card : ℝ) *
            ∑ v : Fin n → Fin 3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2 := by
          exact_mod_cast hcs
      _ = 3 ^ n * ∑ v : Fin n → Fin 3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2 := by
          congr 1
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin]
          push_cast
          ring
  calc (∫ x : R3, ‖iteratedFDeriv ℝ n (⇑φ) x‖ ^ 2)
      ≤ ∫ x : R3, 3 ^ n * ∑ v : Fin n → Fin 3,
          ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2 := by
        refine integral_mono (integrable_opEnergy n φ) ?_ hsum
        exact (integrable_finsetSum _ fun v _ =>
          integrable_tuple_sq n v φ).const_mul _
    _ = 3 ^ n * ∑ v : Fin n → Fin 3, ∫ x : R3,
          ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun v _ => integrable_tuple_sq n v φ]

/-- Order-`n` comparison, lower half: the tuple-sum energy is at most `3ⁿ` times the
operator-norm energy. -/
theorem tupleEnergy_le_opEnergy (n : ℕ) (φ : R3SchwartzVelocity) :
    r3TSelTupleEnergy n φ ≤ 3 ^ n * r3TSelOpEnergy n φ := by
  unfold r3TSelTupleEnergy r3TSelOpEnergy
  have hterm : ∀ v : Fin n → Fin 3,
      (∫ x : R3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2) ≤
        ∫ x : R3, ‖iteratedFDeriv ℝ n (⇑φ) x‖ ^ 2 := by
    intro v
    refine integral_mono (integrable_tuple_sq n v φ) (integrable_opEnergy n φ) fun x => ?_
    have h1 : ‖(∂^{r3TSelTupleDirections v} φ) x‖ ≤ ‖iteratedFDeriv ℝ n (⇑φ) x‖ := by
      rw [r3TSel_iteratedLineDerivOp_eq]
      exact norm_tuple_le_multilinear_norm _ v
    nlinarith [norm_nonneg ((∂^{r3TSelTupleDirections v} φ) x)]
  have hconst : (∑ _v : Fin n → Fin 3, ∫ x : R3, ‖iteratedFDeriv ℝ n (⇑φ) x‖ ^ 2) =
      3 ^ n * ∫ x : R3, ‖iteratedFDeriv ℝ n (⇑φ) x‖ ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  exact (Finset.sum_le_sum fun v _ => hterm v).trans_eq hconst

/-! ## The carrier norm as a frequency integral -/

set_option maxHeartbeats 1000000 in
/-- The squared carrier norm of the canonical order-three coordinate is the cubed-weight
frequency energy. -/
theorem sq_norm_r3SchwartzToHsCLM_three (φ : R3SchwartzVelocity) :
    ‖r3SchwartzToHsCLM 3 φ‖ ^ 2 =
      ∫ ξ : R3, (1 + ‖ξ‖ ^ 2) ^ 3 * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by
  rw [r3SchwartzToHsCLM_apply, ← Lp.norm_fourier_eq, SchwartzMap.toLp_fourier_eq,
    fourier_r3SchwartzBesselCoordinate]
  have hnorm : ‖(r3SchwartzSobolevFrequencyCoordinate 3 φ).toLp 2‖ ^ 2 =
      ∫ ξ : R3, ‖r3SchwartzSobolevFrequencyCoordinate 3 φ ξ‖ ^ 2 := by
    rw [SchwartzMap.norm_toLp]
    exact sq_toReal_eLpNorm_two ((r3SchwartzSobolevFrequencyCoordinate 3 φ).memLp 2)
  rw [hnorm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖r3SchwartzSobolevFrequencyCoordinate 3 φ ξ‖ ^ 2 =
    (1 + ‖ξ‖ ^ 2) ^ 3 * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2
  have happ : r3SchwartzSobolevFrequencyCoordinate 3 φ ξ =
      Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((3 : ℝ) / 2)) •
        (𝓕 φ : R3SchwartzVelocity) ξ := by
    unfold r3SchwartzSobolevFrequencyCoordinate
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rw [happ, norm_smul,
    Complex.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ ((3 : ℝ) / 2)) 2,
    ← Real.rpow_mul (by positivity)]
  norm_num

/-! ## The weight comparison and final assembly -/

/-- Pointwise lower weight bound: `(1/3)(1+r²)³ ≤ ∑_{n ≤ 3} (2π)^{2n} r^{2n}`. -/
theorem weight_lower (r : ℝ) :
    (1 / 3) * (1 + r ^ 2) ^ 3 ≤
      ∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * (r ^ (2 * n)) := by
  have hpi : (1 : ℝ) ≤ 2 * π := by nlinarith [pi_gt_three]
  have hterm : ∀ n ∈ Finset.range 4, r ^ (2 * n) ≤ (2 * π) ^ (2 * n) * r ^ (2 * n) := by
    intro n _
    have h0 : (0 : ℝ) ≤ r ^ (2 * n) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg r) n
    have h1 : (1 : ℝ) ≤ (2 * π) ^ (2 * n) := one_le_pow₀ hpi
    nlinarith
  have hsum : (∑ n ∈ Finset.range 4, r ^ (2 * n)) ≤
      ∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * r ^ (2 * n) :=
    Finset.sum_le_sum hterm
  refine le_trans ?_ hsum
  have hexp : (∑ n ∈ Finset.range 4, r ^ (2 * n)) =
      1 + r ^ 2 + (r ^ 2) ^ 2 + (r ^ 2) ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    ring
  rw [hexp]
  nlinarith [sq_nonneg r, sq_nonneg (r ^ 2), pow_nonneg (sq_nonneg r) 3]

/-- Pointwise upper weight bound: `∑_{n ≤ 3} (2π)^{2n} r^{2n} ≤ (2π)⁶ (1+r²)³`. -/
theorem weight_upper (r : ℝ) :
    (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * (r ^ (2 * n))) ≤
      (2 * π) ^ 6 * (1 + r ^ 2) ^ 3 := by
  have hpi : (1 : ℝ) ≤ 2 * π := by nlinarith [pi_gt_three]
  have hmono : ∀ n ∈ Finset.range 4, (2 * π) ^ (2 * n) ≤ (2 * π) ^ 6 := by
    intro n hn
    have hn4 : n < 4 := Finset.mem_range.mp hn
    exact pow_le_pow_right₀ hpi (by omega)
  have hterm : ∀ n ∈ Finset.range 4,
      (2 * π) ^ (2 * n) * r ^ (2 * n) ≤ (2 * π) ^ 6 * r ^ (2 * n) := by
    intro n hn
    have h0 : (0 : ℝ) ≤ r ^ (2 * n) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg r) n
    exact mul_le_mul_of_nonneg_right (hmono n hn) h0
  have hsum := Finset.sum_le_sum hterm
  refine hsum.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hexp : (∑ n ∈ Finset.range 4, r ^ (2 * n)) =
      1 + r ^ 2 + (r ^ 2) ^ 2 + (r ^ 2) ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    ring
  rw [hexp]
  nlinarith [sq_nonneg r, sq_nonneg (r ^ 2), pow_nonneg (sq_nonneg r) 3]

/-- The total tuple energy across orders `0..3` as a frequency integral, compared
two-sidedly with the squared carrier norm. -/
theorem sum_tupleEnergies_comparison (φ : R3SchwartzVelocity) :
    (1 / 3) * ‖r3SchwartzToHsCLM 3 φ‖ ^ 2 ≤
        (∑ n ∈ Finset.range 4, r3TSelTupleEnergy n φ) ∧
      (∑ n ∈ Finset.range 4, r3TSelTupleEnergy n φ) ≤
        (2 * π) ^ 6 * ‖r3SchwartzToHsCLM 3 φ‖ ^ 2 := by
  have hInt2 : ∀ n : ℕ, Integrable (fun ξ : R3 =>
      (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) *
        ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) volume := by
    intro n
    have h := (integrable_pow_mul_norm_sq_fourier φ (2 * n)).const_mul
      ((2 * π) ^ (2 * n))
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    show (2 * π) ^ (2 * n) * (‖ξ‖ ^ (2 * n) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) =
      (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2
    ring
  have hfreq : (∑ n ∈ Finset.range 4, r3TSelTupleEnergy n φ) =
      ∫ ξ : R3, (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n)) *
        ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by
    have h1 : ∀ n ∈ Finset.range 4, r3TSelTupleEnergy n φ =
        ∫ ξ : R3, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) *
          ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by
      intro n _
      unfold r3TSelTupleEnergy
      rw [sum_tuple_energies n φ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show (2 * π) ^ (2 * n) * (‖ξ‖ ^ (2 * n) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) =
        (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2
      ring
    calc (∑ n ∈ Finset.range 4, r3TSelTupleEnergy n φ)
        = ∑ n ∈ Finset.range 4, ∫ ξ : R3, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) *
            ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := Finset.sum_congr rfl h1
      _ = ∫ ξ : R3, ∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) *
            ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 :=
          (integral_finsetSum _ (fun n _ => hInt2 n)).symm
      _ = ∫ ξ : R3, (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n)) *
            ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
          show (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) *
              ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) =
            (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n)) *
              ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2
          rw [Finset.sum_mul]
  have hint : Integrable (fun ξ : R3 =>
      (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n)) *
        ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) volume := by
    have h2 : Integrable (fun ξ : R3 => ∑ n ∈ Finset.range 4,
        (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) *
          ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) volume :=
      integrable_finsetSum _ (fun n _ => hInt2 n)
    refine h2.congr (Filter.Eventually.of_forall fun ξ => ?_)
    show (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) *
        ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) =
      (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n)) *
        ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2
    rw [Finset.sum_mul]
  have hcarrier : Integrable (fun ξ : R3 =>
      (1 + ‖ξ‖ ^ 2) ^ 3 * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) volume := by
    have hpoly : ∀ ξ : R3, (1 + ‖ξ‖ ^ 2) ^ 3 * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 =
        ∑ n ∈ Finset.range 4, (Nat.choose 3 n : ℝ) *
          (‖ξ‖ ^ (2 * n) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) := by
      intro ξ
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      norm_num
      ring
    refine (integrable_finsetSum _ (fun n _ =>
      (integrable_pow_mul_norm_sq_fourier φ (2 * n)).const_mul
        ((Nat.choose 3 n : ℝ)))).congr
      (Filter.Eventually.of_forall fun ξ => (hpoly ξ).symm)
  constructor
  · rw [hfreq, sq_norm_r3SchwartzToHsCLM_three, ← integral_const_mul]
    refine integral_mono (hcarrier.const_mul _) hint fun ξ => ?_
    have h := weight_lower ‖ξ‖
    have h0 : (0 : ℝ) ≤ ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := sq_nonneg _
    calc (1 / 3) * ((1 + ‖ξ‖ ^ 2) ^ 3 * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2)
        = ((1 / 3) * (1 + ‖ξ‖ ^ 2) ^ 3) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := by ring
      _ ≤ (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n)) *
            ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h h0
  · rw [hfreq, sq_norm_r3SchwartzToHsCLM_three, ← integral_const_mul]
    refine integral_mono hint (hcarrier.const_mul _) fun ξ => ?_
    have h := weight_upper ‖ξ‖
    have h0 : (0 : ℝ) ≤ ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 := sq_nonneg _
    calc (∑ n ∈ Finset.range 4, (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n)) *
          ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2
        ≤ ((2 * π) ^ 6 * (1 + ‖ξ‖ ^ 2) ^ 3) * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h h0
      _ = (2 * π) ^ 6 * ((1 + ‖ξ‖ ^ 2) ^ 3 * ‖(𝓕 φ : R3SchwartzVelocity) ξ‖ ^ 2) := by
          ring

/-- The statement quantity of `R3TSelClassicalSobolevComparability` coincides with the
sum of operator-norm energies. -/
theorem sq_eLpNorm_sum_eq (φ : R3SchwartzVelocity) :
    (∑ n ∈ Finset.range 4,
        ((eLpNorm (iteratedFDeriv ℝ n (⇑φ)) 2 volume).toReal) ^ 2) =
      ∑ n ∈ Finset.range 4, r3TSelOpEnergy n φ :=
  Finset.sum_congr rfl fun n _ => by
    rw [sq_toReal_eLpNorm_two (memLp_two_iteratedFDeriv n φ)]
    rfl

set_option maxHeartbeats 800000 in
/-- **SEL-1 discharged**: the classical Sobolev comparability holds with the explicit
constants `c₁ = 1/(3·81) = 1/243`-grade bounds — precisely, `c₁ = (1/3)·(1/27)` and
`c₂ = 27·(2π)⁶`. -/
theorem r3TSel_classicalSobolevComparability : R3TSelClassicalSobolevComparability := by
  refine ⟨(1 / 3) * (1 / 27), 27 * (2 * π) ^ 6, by norm_num, by positivity, fun φ => ?_⟩
  have hcomp := sum_tupleEnergies_comparison φ
  have hup : ∀ n ∈ Finset.range 4, r3TSelOpEnergy n φ ≤ 27 * r3TSelTupleEnergy n φ := by
    intro n hn
    have hn4 : n < 4 := Finset.mem_range.mp hn
    refine (opEnergy_le_tupleEnergy n φ).trans ?_
    have h27 : (3 : ℝ) ^ n ≤ 27 := by
      calc (3 : ℝ) ^ n ≤ 3 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 27 := by norm_num
    have htup0 : 0 ≤ r3TSelTupleEnergy n φ := by
      unfold r3TSelTupleEnergy
      exact Finset.sum_nonneg fun v _ => integral_nonneg fun x => sq_nonneg _
    exact mul_le_mul_of_nonneg_right h27 htup0
  have hlow : ∀ n ∈ Finset.range 4,
      (1 / 27) * r3TSelTupleEnergy n φ ≤ r3TSelOpEnergy n φ := by
    intro n hn
    have hn4 : n < 4 := Finset.mem_range.mp hn
    have h := tupleEnergy_le_opEnergy n φ
    have h27 : (3 : ℝ) ^ n ≤ 27 := by
      calc (3 : ℝ) ^ n ≤ 3 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 27 := by norm_num
    have hop0 := r3TSelOpEnergy_nonneg n φ
    nlinarith
  refine ⟨fun n _ => memLp_two_iteratedFDeriv n φ, ?_, ?_⟩
  · rw [sq_eLpNorm_sum_eq]
    have h1 : (1 / 27 : ℝ) * ∑ n ∈ Finset.range 4, r3TSelTupleEnergy n φ ≤
        ∑ n ∈ Finset.range 4, r3TSelOpEnergy n φ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hlow
    have h2 : (1 / 3 : ℝ) * ‖r3SchwartzToHsCLM 3 φ‖ ^ 2 ≤
        ∑ n ∈ Finset.range 4, r3TSelTupleEnergy n φ := hcomp.1
    nlinarith
  · rw [sq_eLpNorm_sum_eq]
    have h1 : (∑ n ∈ Finset.range 4, r3TSelOpEnergy n φ) ≤
        27 * ∑ n ∈ Finset.range 4, r3TSelTupleEnergy n φ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hup
    have h2 := hcomp.2
    nlinarith

end

end MNS2
