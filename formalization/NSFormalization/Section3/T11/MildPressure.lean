import NSFormalization.Section3.T11.ClassicalAssembly
import NSFormalization.Section3.T10.ForcePaths

/-! # The pressure of a persistent mild torus solution

The construction is the Leray complement of the physical source
`S = f - ∇·(u⊗u)`: at every nonzero lattice frequency the scalar `p̂(k)` is the
unique solution of `2πi k p̂(k) = (I - P) Ŝ(k)`, with `P` the periodic Leray
symbol of `Section3/T10/Leray.lean`, and the zero mode is set to zero (the
pressure gauge).  The physical pressure is the scalar Fourier inversion of that
coefficient family.
-/
noncomputable section
namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NSFormalization.Section3.T10
open scoped BigOperators ContDiff ComplexConjugate NNReal

local instance mildPressureNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance mildPressureNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. Weighted summability of smooth periodic Fourier coefficients -/

theorem mildPressure_weight_pos (k : PeriodicFrequency) :
    0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight; positivity

/-- Rapid decay at two extra orders plus the summable inverse square weight give
genuine polynomially weighted absolute summability. -/
theorem summable_weight_pow_mul_coeff {f : Space → ℂ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (N : ℕ) :
    Summable (fun k ↦ periodicFrequencyWeight k ^ N * ‖periodicFourierCoeff f k‖) := by
  obtain ⟨C, hC⟩ := periodicFourierCoeff_rapid_decay hp hs (N + 2)
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_)
    (summable_inverse_periodicFrequencyWeight.mul_left C)
  · exact mul_nonneg (pow_nonneg (mildPressure_weight_pos k).le _) (norm_nonneg _)
  · have hw := mildPressure_weight_pos k
    have he : periodicFrequencyWeight k ^ N * ‖periodicFourierCoeff f k‖ =
        (periodicFrequencyWeight k ^ (N + 2) * ‖periodicFourierCoeff f k‖) *
          (periodicFrequencyWeight k ^ 2)⁻¹ := by
      rw [pow_add]
      field_simp [hw.ne']
    rw [he]
    exact mul_le_mul_of_nonneg_right (hC k) (by positivity)

/-! ## 2. Scalar Fourier series on the unit torus -/

/-- The scalar Fourier series attached to a coefficient family. -/
def torusScalarSeries (c : PeriodicFrequency → ℂ) (x : Space) : ℂ :=
  ∑' k, c k * NSFormalization.Paper1.periodicCharacter k x

theorem torusScalarSeries_summable {c : PeriodicFrequency → ℂ}
    (hc : Summable (fun k ↦ ‖c k‖)) (x : Space) :
    Summable (fun k ↦ c k * NSFormalization.Paper1.periodicCharacter k x) := by
  apply Summable.of_norm
  simpa only [norm_mul, torusCharacter_norm, mul_one] using hc

theorem torusScalarSeries_periodic (c : PeriodicFrequency → ℂ) :
    IsPeriodicSpatial (torusScalarSeries c) := by
  intro x j
  unfold torusScalarSeries
  exact tsum_congr fun k ↦ by
    rw [NSFormalization.Paper1.periodicCharacter_periodic k x j]

/-- Conjugate reflection of the coefficients makes the series real. -/
theorem torusScalarSeries_conj {c : PeriodicFrequency → ℂ}
    (hneg : ∀ k, c (-k) = star (c k)) (x : Space) :
    conj (torusScalarSeries c x) = torusScalarSeries c x := by
  unfold torusScalarSeries
  rw [Complex.conj_tsum]
  have he (k : PeriodicFrequency) :
      conj (c k * NSFormalization.Paper1.periodicCharacter k x) =
        c (-k) * NSFormalization.Paper1.periodicCharacter (-k) x := by
    rw [map_mul, hneg]
    simp only [NSFormalization.Paper1.periodicCharacter_eq_mFourier, UnitAddTorus.mFourier_neg]
    rfl
  simp_rw [he]
  exact (Equiv.neg PeriodicFrequency).tsum_eq
    (fun k ↦ c k * NSFormalization.Paper1.periodicCharacter k x)

/-- Quotient-torus expression of the series. -/
theorem torusScalarSeries_lift (c : PeriodicFrequency → ℂ) (q : PeriodicTorus) :
    torusLift (torusScalarSeries c) q = ∑' k, c k * UnitAddTorus.mFourier k q := by
  have hz := (UnitAddTorus.measurableEquivPiIoc
    (0 : NavierStokes.PeriodicIntegration.Coords)).symm_apply_apply q
  change (fun j ↦ (((UnitAddTorus.measurableEquivPiIoc
    (0 : NavierStokes.PeriodicIntegration.Coords) q).val j : ℝ) : UnitAddCircle)) = q at hz
  simp only [torusLift, NSFormalization.Paper1.torusLift, torusScalarSeries,
    NSFormalization.Paper1.periodicCharacter_eq_mFourier,
    NavierStokes.PeriodicIntegration.toSpace_apply, hz]

/-- Inversion recovers the coefficients of an absolutely convergent series. -/
theorem torusScalarSeries_coeff {c : PeriodicFrequency → ℂ}
    (hc : Summable (fun k ↦ ‖c k‖)) (k : PeriodicFrequency) :
    periodicFourierCoeff (torusScalarSeries c) k = c k := by
  let f : PeriodicFrequency → PeriodicTorus → ℂ := fun l q ↦
    c l * UnitAddTorus.mFourier (l - k) q
  have hf (l : PeriodicFrequency) : Integrable (f l) periodicTorusMeasure := by
    have hcont : Continuous (f l) :=
      continuous_const.mul (UnitAddTorus.mFourier (l - k)).continuous
    simpa only [integrableOn_univ] using hcont.continuousOn.integrableOn_compact
      (μ := periodicTorusMeasure) isCompact_univ
  have hnorm (l : PeriodicFrequency) (q : PeriodicTorus) : ‖f l q‖ = ‖c l‖ := by
    simp only [f, norm_mul, torusMFourier_norm, mul_one]
  have hs : Summable (fun l ↦ ∫ q, ‖f l q‖ ∂periodicTorusMeasure) := by
    simpa only [hnorm, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
      one_smul] using hc
  change (∫ q, UnitAddTorus.mFourier (-k) q •
    torusLift (torusScalarSeries c) q ∂periodicTorusMeasure) = _
  simp_rw [torusScalarSeries_lift, smul_eq_mul, ← tsum_mul_left]
  have he (q : PeriodicTorus) (l : PeriodicFrequency) :
      UnitAddTorus.mFourier (-k) q * (c l * UnitAddTorus.mFourier l q) = f l q := by
    simp only [f, sub_eq_add_neg, UnitAddTorus.mFourier_add]
    ring
  simp_rw [he]
  rw [← integral_tsum_of_summable_integral_norm hf hs]
  simp only [f, integral_const_mul, integral_mFourier, sub_eq_zero, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq k _

-- The multilinear derivative bound of every Fourier character is reused at all orders.
set_option maxHeartbeats 400000 in
/-- All-order weighted summability makes the scalar series smooth. -/
theorem torusScalarSeries_contDiff {c : PeriodicFrequency → ℂ}
    (hc : ∀ N : ℕ, Summable (fun k ↦ periodicFrequencyWeight k ^ N * ‖c k‖)) :
    ContDiff ℝ ∞ (torusScalarSeries c) := by
  apply contDiff_tsum (v := fun n k ↦ 3 ^ n * (periodicFrequencyWeight k ^ n * ‖c k‖))
  · intro k
    exact contDiff_const.mul (NSFormalization.Paper1.periodicCharacter_smooth k)
  · intro n _
    exact (hc n).mul_left _
  · intro n k x _
    have he : (fun y ↦ c k * NSFormalization.Paper1.periodicCharacter k y) =
        c k • NSFormalization.Paper1.periodicCharacter k := rfl
    rw [he, iteratedFDeriv_const_smul_apply
      ((NSFormalization.Paper1.periodicCharacter_smooth k).of_le (by simp)).contDiffAt,
      norm_smul]
    calc
      _ ≤ ‖c k‖ * ‖NSFormalization.Paper1.periodicPhase k‖ ^ n :=
        mul_le_mul_of_nonneg_left (assembly_character_derivative_bound k n x) (norm_nonneg _)
      _ ≤ ‖c k‖ * (3 * periodicFrequencyWeight k) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (assembly_phase_norm_le k) n)
          (norm_nonneg _)
      _ = _ := by rw [mul_pow]; ring

/-! ## 3. The Leray-complement scalar potential of a physical source -/

/-- The unweighted Fourier coefficient of one component of a physical field. -/
def sourceComponentCoeff (S : SpatialField) (j : Fin 3) (k : PeriodicFrequency) : ℂ :=
  periodicFourierCoeff (fun x ↦ ((S x j : ℝ) : ℂ)) k

/-- `Section3/T10/Leray.lean`'s symbol is `A - (k/|k|²)(k·A)`; its complement at
a nonzero frequency is `(k/|k|²)(k·A)`, which is `2πi k` times the scalar below.
The zero mode is the gauge choice `0`. -/
def lerayPotentialCoeff (S : SpatialField) (k : PeriodicFrequency) : ℂ :=
  if k = 0 then 0
  else (∑ j : Fin 3, (k j : ℂ) * sourceComponentCoeff S j k) /
    ((2 * Real.pi * Complex.I) * ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ))

theorem lerayPotentialCoeff_zero (S : SpatialField) : lerayPotentialCoeff S 0 = 0 := by
  simp [lerayPotentialCoeff]

theorem mildPressure_one_le_sq_sum {k : PeriodicFrequency} (hk : k ≠ 0) :
    1 ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  have h1 : (1 : ℝ) ≤ (k j : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ |k j| := Int.one_le_abs (by simpa using hj)
    have h2 : (1 : ℝ) ≤ |(k j : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast this
    nlinarith [abs_nonneg ((k j : ℝ)), sq_abs ((k j : ℝ))]
  exact h1.trans (Finset.single_le_sum (f := fun i : Fin 3 ↦ (k i : ℝ) ^ 2)
    (fun i _ ↦ sq_nonneg _) (Finset.mem_univ j))

theorem mildPressure_abs_le_sq_sum (k : PeriodicFrequency) (j : Fin 3) :
    |(k j : ℝ)| ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  have hj : |(k j : ℝ)| ≤ (k j : ℝ) ^ 2 := by
    rcases eq_or_ne (k j) 0 with h | h
    · simp [h]
    · have : (1 : ℤ) ≤ |k j| := Int.one_le_abs h
      have h2 : (1 : ℝ) ≤ |(k j : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast this
      nlinarith [abs_nonneg ((k j : ℝ)), sq_abs ((k j : ℝ))]
  exact hj.trans (Finset.single_le_sum (f := fun i : Fin 3 ↦ (k i : ℝ) ^ 2)
    (fun i _ ↦ sq_nonneg _) (Finset.mem_univ j))

theorem norm_lerayPotentialCoeff_le (S : SpatialField) (k : PeriodicFrequency) :
    ‖lerayPotentialCoeff S k‖ ≤ ∑ j : Fin 3, ‖sourceComponentCoeff S j k‖ := by
  unfold lerayPotentialCoeff
  split_ifs with hk
  · simpa using Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦ norm_nonneg
      (sourceComponentCoeff S j k))
  · have hD1 : 1 ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 := mildPressure_one_le_sq_sum hk
    have hDpos : 0 < ∑ j : Fin 3, (k j : ℝ) ^ 2 := lt_of_lt_of_le one_pos hD1
    have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hden : ‖(2 * Real.pi * Complex.I) * ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)‖ =
        2 * Real.pi * ∑ j : Fin 3, (k j : ℝ) ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul]
      simp only [Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_ofNat, abs_of_pos Real.pi_pos, abs_of_pos hDpos]
    rw [norm_div, hden, div_le_iff₀ (by positivity)]
    calc ‖∑ j : Fin 3, (k j : ℂ) * sourceComponentCoeff S j k‖
        ≤ ∑ j : Fin 3, ‖(k j : ℂ) * sourceComponentCoeff S j k‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3, (2 * Real.pi * ∑ i : Fin 3, (k i : ℝ) ^ 2) *
            ‖sourceComponentCoeff S j k‖ := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have hb : ‖(k j : ℂ)‖ = |(k j : ℝ)| := by
            simp [Complex.norm_intCast]
          rw [hb]
          calc |(k j : ℝ)| ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := mildPressure_abs_le_sq_sum k j
            _ ≤ 2 * Real.pi * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by nlinarith
      _ = (∑ j : Fin 3, ‖sourceComponentCoeff S j k‖) *
            (2 * Real.pi * ∑ i : Fin 3, (k i : ℝ) ^ 2) := by
          rw [← Finset.mul_sum]
          ring

theorem lerayPotentialCoeff_neg (S : SpatialField) (k : PeriodicFrequency) :
    lerayPotentialCoeff S (-k) = star (lerayPotentialCoeff S k) := by
  by_cases hk : k = 0
  · subst hk
    simp [lerayPotentialCoeff]
  · have hnk : (-k) ≠ 0 := neg_ne_zero.mpr hk
    have hsq : (∑ j : Fin 3, (((-k) j : ℤ) : ℝ) ^ 2) = ∑ j : Fin 3, ((k j : ℤ) : ℝ) ^ 2 := by
      simp
    have hc (j : Fin 3) : sourceComponentCoeff S j (-k) = star (sourceComponentCoeff S j k) :=
      periodicFourierCoeff_real_neg (fun x ↦ S x j) k
    have hden : star ((2 * Real.pi * Complex.I) *
        ((∑ j : Fin 3, ((k j : ℤ) : ℝ) ^ 2 : ℝ) : ℂ)) =
        -((2 * Real.pi * Complex.I) * ((∑ j : Fin 3, ((k j : ℤ) : ℝ) ^ 2 : ℝ) : ℂ)) := by
      simp only [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal,
        map_ofNat]
      ring
    have hnum : (∑ j : Fin 3, (((-k) j : ℤ) : ℂ) * sourceComponentCoeff S j (-k)) =
        -star (∑ j : Fin 3, ((k j : ℤ) : ℂ) * sourceComponentCoeff S j k) := by
      rw [star_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hc j, star_mul']
      simp only [Pi.neg_apply, Int.cast_neg, Complex.star_def, map_intCast]
      ring
    simp only [lerayPotentialCoeff, hk, hnk, ↓reduceIte]
    rw [star_div₀, hden, hnum, hsq, neg_div, div_neg]

/-- The defining Leray-complement identity at the level of raw coefficients. -/
theorem periodicDerivativeSymbol_mul_lerayPotentialCoeff (S : SpatialField)
    {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicDerivativeSymbol i k * lerayPotentialCoeff S k =
      ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∑ j : Fin 3, (k j : ℂ) * sourceComponentCoeff S j k := by
  have hDpos : 0 < ∑ j : Fin 3, (k j : ℝ) ^ 2 :=
    lt_of_lt_of_le one_pos (mildPressure_one_le_sq_sum hk)
  have hD : ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hDpos.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [lerayPotentialCoeff, hk, ↓reduceIte, periodicDerivativeSymbol]
  field_simp

/-- Exactly the Leray complement of the source datum, in the T10 symbol. -/
theorem lerayPotentialCoeff_leray_complement {s : ℝ} {S : SpatialField}
    {B : PeriodicSobolev s} (hB : IsPeriodicDatum s S B)
    {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicDerivativeSymbol i k * lerayPotentialCoeff S k =
      torusPhysicalCoeff s B i k -
        ((periodicFrequencyWeight k ^ (-s / 2) : ℝ) : ℂ) * periodicLeray s B i k := by
  have hcoeff (j : Fin 3) : torusPhysicalCoeff s B j k = sourceComponentCoeff S j k :=
    torusPhysicalCoeff_eq hB j k
  have hL : ((periodicFrequencyWeight k ^ (-s / 2) : ℝ) : ℂ) * periodicLeray s B i k =
      sourceComponentCoeff S i k -
        ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
          ∑ j : Fin 3, (k j : ℂ) * sourceComponentCoeff S j k := by
    simp only [periodicLeray, hk, ↓reduceIte, mul_sub]
    congr 1
    · rw [← hcoeff i]
      rfl
    · have hterm (j : Fin 3) : (k j : ℂ) * sourceComponentCoeff S j k =
          ((periodicFrequencyWeight k ^ (-s / 2) : ℝ) : ℂ) * ((k j : ℂ) * B.1 j k) := by
        rw [← hcoeff j, torusPhysicalCoeff]
        ring
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      ring
  rw [periodicDerivativeSymbol_mul_lerayPotentialCoeff S hk i, hL, ← hcoeff i]
  ring

/-! ## 4. The scalar potential, its regularity, gauge and gradient -/

theorem sourceComponent_contDiff {S : SpatialField} (hS : ContDiff ℝ ∞ S) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ ((S x j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hS)

theorem sourceComponent_periodic {S : SpatialField} (hp : IsPeriodicSpatial S) (j : Fin 3) :
    IsPeriodicSpatial (fun x ↦ ((S x j : ℝ) : ℂ)) :=
  fun x l ↦ congrArg (fun y : Space ↦ ((y j : ℝ) : ℂ)) (hp x l)

theorem summable_weight_pow_mul_lerayPotentialCoeff {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) (N : ℕ) :
    Summable (fun k ↦ periodicFrequencyWeight k ^ N * ‖lerayPotentialCoeff S k‖) := by
  have hsum : Summable (fun k ↦ ∑ j : Fin 3, periodicFrequencyWeight k ^ N *
      ‖sourceComponentCoeff S j k‖) :=
    summable_sum (fun j _ ↦ summable_weight_pow_mul_coeff (sourceComponent_periodic hp j)
      (sourceComponent_contDiff hS j) N)
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hsum
  · exact mul_nonneg (pow_nonneg (mildPressure_weight_pos k).le _) (norm_nonneg _)
  · calc periodicFrequencyWeight k ^ N * ‖lerayPotentialCoeff S k‖
        ≤ periodicFrequencyWeight k ^ N * ∑ j : Fin 3, ‖sourceComponentCoeff S j k‖ :=
          mul_le_mul_of_nonneg_left (norm_lerayPotentialCoeff_le S k)
            (pow_nonneg (mildPressure_weight_pos k).le _)
      _ = _ := Finset.mul_sum _ _ _

theorem lerayPotentialCoeff_summable {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) :
    Summable (fun k ↦ ‖lerayPotentialCoeff S k‖) := by
  simpa using summable_weight_pow_mul_lerayPotentialCoeff hS hp 0

/-- The physical Leray-complement potential of a periodic source field. -/
def lerayPotential (S : SpatialField) (x : Space) : ℝ :=
  (torusScalarSeries (lerayPotentialCoeff S) x).re

theorem ofReal_lerayPotential (S : SpatialField) (x : Space) :
    ((lerayPotential S x : ℝ) : ℂ) = torusScalarSeries (lerayPotentialCoeff S) x :=
  Complex.conj_eq_iff_re.mp (torusScalarSeries_conj (lerayPotentialCoeff_neg S) x)

theorem lerayPotential_periodic (S : SpatialField) : IsPeriodicSpatial (lerayPotential S) :=
  fun x j ↦ congrArg Complex.re (torusScalarSeries_periodic (lerayPotentialCoeff S) x j)

theorem lerayPotential_contDiff {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) :
    ContDiff ℝ ∞ (lerayPotential S) :=
  Complex.reCLM.contDiff.comp
    (torusScalarSeries_contDiff (summable_weight_pow_mul_lerayPotentialCoeff hS hp))

theorem lerayPotential_coeff {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) k = lerayPotentialCoeff S k := by
  have he : (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) =
      torusScalarSeries (lerayPotentialCoeff S) := funext (ofReal_lerayPotential S)
  rw [he]
  exact torusScalarSeries_coeff (lerayPotentialCoeff_summable hS hp) k

theorem lerayPotential_complex_contDiff {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) :
    ContDiff ℝ ∞ (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (lerayPotential_contDiff hS hp)

theorem lerayPotential_complex_periodic (S : SpatialField) :
    IsPeriodicSpatial (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) :=
  fun x j ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (lerayPotential_periodic S x j)

theorem lerayPotential_torusLift_continuous {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) :
    Continuous (torusLift (lerayPotential S)) := by
  have hcC : Continuous (torusLift (fun x ↦ ((lerayPotential S x : ℝ) : ℂ))) := by
    apply NSFormalization.Paper1.continuous_torusLift
      (lerayPotential_complex_contDiff hS hp).continuous
    intro x j
    exact lerayPotential_complex_periodic S x j
  have he : torusLift (lerayPotential S) =
      fun q ↦ (torusLift (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) q).re := rfl
  rw [he]
  exact Complex.continuous_re.comp hcC

theorem lerayPotential_integrable {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) :
    Integrable (torusLift (lerayPotential S)) periodicTorusMeasure := by
  simpa using (lerayPotential_torusLift_continuous hS hp).continuousOn.integrableOn_compact
    (μ := periodicTorusMeasure) isCompact_univ

/-- The gauge: the Leray potential has vanishing normalized torus mean. -/
theorem lerayPotential_mean {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) :
    ∫ y : PeriodicTorus, torusLift (lerayPotential S) y ∂periodicTorusMeasure = 0 := by
  have h0 : periodicFourierCoeff (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) 0 = 0 := by
    rw [lerayPotential_coeff hS hp 0, lerayPotentialCoeff_zero]
  have hc : ((∫ y : PeriodicTorus, torusLift (lerayPotential S) y ∂periodicTorusMeasure : ℝ) : ℂ)
      = periodicFourierCoeff (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) 0 := by
    change _ = UnitAddTorus.mFourierCoeff
      (fun y : PeriodicTorus ↦ ((torusLift (lerayPotential S) y : ℝ) : ℂ)) 0
    unfold UnitAddTorus.mFourierCoeff
    simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]
    simpa only [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.integral_comp_comm (lerayPotential_integrable hS hp)).symm
  rw [h0] at hc
  exact_mod_cast hc

/-- Every component of the potential gradient has the exact Leray-complement datum. -/
theorem lerayPotential_gradient_coeff {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff
      (fun x ↦ ((fderiv ℝ (lerayPotential S) x (coordinateVector i) : ℝ) : ℂ)) k =
      periodicDerivativeSymbol i k * lerayPotentialCoeff S k := by
  have hL := lerayPotential_contDiff hS hp
  have hLc : ContDiff ℝ ∞ (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) :=
    lerayPotential_complex_contDiff hS hp
  have hLp : IsPeriodicSpatial (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) :=
    lerayPotential_complex_periodic S
  have he : (fun x ↦ ((fderiv ℝ (lerayPotential S) x (coordinateVector i) : ℝ) : ℂ)) =
      spatialPartial i (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) :=
    (spatialPartial_complexify (hL.of_le (by simp)) i).symm
  have hstep : periodicFourierCoeff
      (spatialPartial i (fun x ↦ ((lerayPotential S x : ℝ) : ℂ))) k =
      periodicDerivativeSymbol i k *
        periodicFourierCoeff (fun x ↦ ((lerayPotential S x : ℝ) : ℂ)) k :=
    periodicFourierCoeff_fderiv hLp (hLc.of_le (by simp)) i k
  rw [he, hstep, lerayPotential_coeff hS hp]

/-! ## 5. The Poisson equation for the potential -/

/-- Two smooth periodic scalars with the same Fourier data are equal. -/
theorem periodic_eq_of_coeff_eq {f g : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpf : IsPeriodicSpatial f)
    (hg : ContDiff ℝ ∞ g) (hpg : IsPeriodicSpatial g)
    (h : ∀ k, periodicFourierCoeff (fun x ↦ ((f x : ℝ) : ℂ)) k =
      periodicFourierCoeff (fun x ↦ ((g x : ℝ) : ℂ)) k) : f = g := by
  have hfc : ContDiff ℝ ∞ (fun x ↦ ((f x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hgc : ContDiff ℝ ∞ (fun x ↦ ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hpfc : IsPeriodicSpatial (fun x ↦ ((f x : ℝ) : ℂ)) :=
    fun x j ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (hpf x j)
  have hpgc : IsPeriodicSpatial (fun x ↦ ((g x : ℝ) : ℂ)) :=
    fun x j ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (hpg x j)
  funext x
  apply Complex.ofReal_inj.mp
  rw [periodic_eq_tsum_mFourier hpfc hfc.continuous
      (summable_periodicFourierCoeff_of_smooth hpfc hfc) x,
    periodic_eq_tsum_mFourier hpgc hgc.continuous
      (summable_periodicFourierCoeff_of_smooth hpgc hgc) x]
  exact tsum_congr (fun k ↦ by rw [h k])

/-- Fourier coefficients of the divergence of a smooth periodic vector field. -/
theorem periodicFourierCoeff_divergence {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) (k : PeriodicFrequency) :
    periodicFourierCoeff
      (fun x ↦ ((∑ j : Fin 3, spatialPartial j (fun y ↦ S y j) x : ℝ) : ℂ)) k =
      ∑ j : Fin 3, periodicDerivativeSymbol j k * sourceComponentCoeff S j k := by
  have hj (j : Fin 3) : ContDiff ℝ ∞ (fun y ↦ S y j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hS
  have hjc (j : Fin 3) : ContDiff ℝ ∞ (fun x ↦ ((S x j : ℝ) : ℂ)) := sourceComponent_contDiff hS j
  have hds (j : Fin 3) : ContDiff ℝ ∞ (spatialPartial j (fun y ↦ ((S y j : ℝ) : ℂ))) :=
    ((hjc j).fderiv_right (by simp)).clm_apply contDiff_const
  have hd (j : Fin 3) : Continuous (spatialPartial j (fun y ↦ ((S y j : ℝ) : ℂ))) :=
    (hds j).continuous
  have hcomplex : (fun x ↦ ((∑ j : Fin 3, spatialPartial j (fun y ↦ S y j) x : ℝ) : ℂ)) =
      fun x ↦ ∑ j : Fin 3, spatialPartial j (fun y ↦ ((S y j : ℝ) : ℂ)) x := by
    funext x
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h1 : ContDiff ℝ 1 (fun y ↦ S y j) := (hj j).of_le (by simp)
    rw [spatialPartial_complexify h1 j]
  rw [hcomplex]
  have he : periodicFourierCoeff (fun x ↦ ∑ j : Fin 3,
      spatialPartial j (fun y ↦ ((S y j : ℝ) : ℂ)) x) k =
        ∑ j : Fin 3, periodicFourierCoeff (spatialPartial j (fun y ↦ ((S y j : ℝ) : ℂ))) k := by
    simp only [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff_eq_cube,
      Finset.mul_sum, NavierStokes.PeriodicIntegration.cubeIntegral]
    apply integral_finsetSum
    intro j _
    exact NavierStokes.PeriodicIntegration.integrable_cube
      ((NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous.mul (hd j))
  rw [he]
  exact Finset.sum_congr rfl fun j _ ↦
    periodicFourierCoeff_fderiv (sourceComponent_periodic hp j) ((hjc j).of_le (by simp)) j k

/-- The Laplace symbol applied to the Leray potential is the divergence symbol
of the source.  This is `-4π²|k|² p̂(k) = 2πi k · Ŝ(k)`. -/
theorem lerayPotentialCoeff_laplace_symbol (S : SpatialField) (k : PeriodicFrequency) :
    (-(4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) * lerayPotentialCoeff S k =
      ∑ j : Fin 3, periodicDerivativeSymbol j k * sourceComponentCoeff S j k := by
  have hsum : ∑ j : Fin 3, periodicDerivativeSymbol j k * sourceComponentCoeff S j k =
      (2 * Real.pi * Complex.I) * ∑ j : Fin 3, (k j : ℂ) * sourceComponentCoeff S j k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by simp only [periodicDerivativeSymbol]; ring
  rw [hsum]
  by_cases hk : k = 0
  · subst hk
    simp [lerayPotentialCoeff]
  · have hDpos : 0 < ∑ j : Fin 3, (k j : ℝ) ^ 2 :=
      lt_of_lt_of_le one_pos (mildPressure_one_le_sq_sum hk)
    have hD : ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hDpos.ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hE : (2 * Real.pi * Complex.I) * ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hD
    have hII : (2 * (Real.pi : ℂ) * Complex.I) * (2 * (Real.pi : ℂ) * Complex.I) =
        -(4 * (Real.pi : ℂ) ^ 2) := by
      calc (2 * (Real.pi : ℂ) * Complex.I) * (2 * (Real.pi : ℂ) * Complex.I)
          = 4 * (Real.pi : ℂ) ^ 2 * (Complex.I * Complex.I) := by ring
        _ = -(4 * (Real.pi : ℂ) ^ 2) := by rw [Complex.I_mul_I]; ring
    have hfac : (-(4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) =
        (2 * Real.pi * Complex.I) *
          ((2 * Real.pi * Complex.I) * ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) := by
      rw [← mul_assoc, hII]
      push_cast
      ring
    simp only [lerayPotentialCoeff, hk, ↓reduceIte]
    rw [hfac, mul_assoc]
    congr 1
    field_simp

/-- **Pressure Poisson equation** for the potential: `Δ p = ∇·S`. -/
theorem lerayPotential_poisson {S : SpatialField}
    (hS : ContDiff ℝ ∞ S) (hp : IsPeriodicSpatial S) (t : ℝ) (x : Space) :
    scalarSpatialLaplacianT (fun z : SpaceTime ↦ lerayPotential S z.2) t x =
      ∑ j : Fin 3, spatialPartial j (fun y ↦ S y j) x := by
  have hL := lerayPotential_contDiff hS hp
  have hLp := lerayPotential_periodic S
  have hEq : (fun y ↦ scalarSpatialLaplacianT (fun z : SpaceTime ↦ lerayPotential S z.2) t y) =
      (fun y ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j (lerayPotential S)) y) :=
    funext fun y ↦ scalarSpatialLaplacianT_eq (lerayPotential S) t y
  have hLapSmooth : ContDiff ℝ ∞
      (fun y ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j (lerayPotential S)) y) := by
    apply ContDiff.sum
    intro j _
    exact NavierStokes.PeriodicUniqueness.spatial_partial_contDiff
      (NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hL j) j
  have hLapPer : IsPeriodicSpatial
      (fun y ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j (lerayPotential S)) y) := by
    intro y l
    exact Finset.sum_congr rfl fun j _ ↦
      NavierStokes.PeriodicUniqueness.spatial_partial_periodic
        (NavierStokes.PeriodicUniqueness.spatial_partial_periodic (fun z q ↦ hLp z q) j) j y l
  have hDivSmooth : ContDiff ℝ ∞ (fun y ↦ ∑ j : Fin 3, spatialPartial j (fun z ↦ S z j) y) := by
    apply ContDiff.sum
    intro j _
    exact NavierStokes.PeriodicUniqueness.spatial_partial_contDiff
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hS) j
  have hDivPer : IsPeriodicSpatial (fun y ↦ ∑ j : Fin 3, spatialPartial j (fun z ↦ S z j) y) := by
    intro y l
    exact Finset.sum_congr rfl fun j _ ↦
      NavierStokes.PeriodicUniqueness.spatial_partial_periodic
        (fun z q ↦ congrArg (fun v : Space ↦ v j) (hp z q)) j y l
  have hcoeff : ∀ k, periodicFourierCoeff
      (fun y ↦ ((∑ j : Fin 3, spatialPartial j (spatialPartial j (lerayPotential S)) y : ℝ) : ℂ)) k
      = periodicFourierCoeff
        (fun y ↦ ((∑ j : Fin 3, spatialPartial j (fun z ↦ S z j) y : ℝ) : ℂ)) k := by
    intro k
    have h1 := periodicFourierCoeff_scalarSpatialLaplacianT hLp (hL.of_le (by norm_num)) t k
    rw [lerayPotential_coeff hS hp] at h1
    have h2 : (fun y ↦ ((scalarSpatialLaplacianT
        (fun z : SpaceTime ↦ lerayPotential S z.2) t y : ℝ) : ℂ)) =
        fun y ↦ ((∑ j : Fin 3,
          spatialPartial j (spatialPartial j (lerayPotential S)) y : ℝ) : ℂ) :=
      funext fun y ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (congrFun hEq y)
    rw [h2] at h1
    rw [h1, periodicFourierCoeff_divergence hS hp k, lerayPotentialCoeff_laplace_symbol S k]
  have hfinal : (fun y ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j (lerayPotential S)) y) =
      (fun y ↦ ∑ j : Fin 3, spatialPartial j (fun z ↦ S z j) y) :=
    periodic_eq_of_coeff_eq hLapSmooth hLapPer hDivSmooth hDivPer hcoeff
  rw [congrFun hEq x]
  exact congrFun hfinal x

/-! ## 6. Physical calculus bridges -/

theorem spatialPartial_sub {f₁ f₂ : Space → ℝ} {x : Space}
    (h1 : DifferentiableAt ℝ f₁ x) (h2 : DifferentiableAt ℝ f₂ x) (j : Fin 3) :
    spatialPartial j (fun y ↦ f₁ y - f₂ y) x = spatialPartial j f₁ x - spatialPartial j f₂ x := by
  have h : HasFDerivAt (fun y ↦ f₁ y - f₂ y) (fderiv ℝ f₁ x - fderiv ℝ f₂ x) x :=
    h1.hasFDerivAt.sub h2.hasFDerivAt
  show fderiv ℝ (fun y ↦ f₁ y - f₂ y) x (coordinateVector j) = _
  rw [h.fderiv]
  rfl

theorem spatialDivergence_eq_sum {w : SpaceTimeField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun y : Space ↦ w (t, y))) (x : Space) :
    spatialDivergence w t x = ∑ j : Fin 3, spatialPartial j (fun y : Space ↦ w (t, y) j) x := by
  unfold spatialDivergence spatialDerivative
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : HasFDerivAt (fun y : Space ↦ w (t, y) j)
      ((EuclideanSpace.proj (𝕜 := ℝ) j).comp (fderiv ℝ (fun y : Space ↦ w (t, y)) x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x
      ((hw.differentiable (by simp) x).hasFDerivAt)
  show (fderiv ℝ (fun y : Space ↦ w (t, y)) x (coordinateVector j)) j =
    fderiv ℝ (fun y : Space ↦ w (t, y) j) x (coordinateVector j)
  rw [h.fderiv]
  rfl

theorem pressureGradient_component (p : SpaceTimeScalar) (t : ℝ) (x : Space) (i : Fin 3) :
    pressureGradient p t x i = fderiv ℝ (fun y : Space ↦ p (t, y)) x (coordinateVector i) := by
  simp [pressureGradient, coordinateVector, Pi.single_apply]

theorem pressureGradient_continuous {p : SpaceTimeScalar} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun y : Space ↦ p (t, y))) :
    Continuous (fun x ↦ pressureGradient p t x) := by
  unfold pressureGradient
  apply continuous_finsetSum
  intro i _
  exact ((NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hp i).continuous).smul
    continuous_const

theorem convectionDivergenceT_spatial_contDiff {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x))) :
    ContDiff ℝ ∞ (fun x ↦ convectionDivergenceT v t x) := by
  have he : (fun x ↦ convectionDivergenceT v t x) = fun x ↦ ∑ j : Fin 3,
      fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x (coordinateVector j) := rfl
  rw [he]
  apply ContDiff.sum
  intro j _
  exact NavierStokes.PeriodicUniqueness.spatial_partial_contDiff
    (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hv).smul hv) j

theorem convectionDivergenceT_spatial_periodic {v : SpaceTimeField} {t : ℝ}
    (hv : IsPeriodicSpatial (fun x : Space ↦ v (t, x))) :
    IsPeriodicSpatial (fun x ↦ convectionDivergenceT v t x) := by
  intro x l
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact congrArg (fun A : Space →L[ℝ] Space ↦ A (coordinateVector j))
    (NavierStokes.PeriodicUniqueness.periodic_fderiv
      (fun y q ↦ congrArg (fun w : Space ↦ (w j) • w) (hv y q)) x l)

/-! ## 7. The pressure of a persistent mild solution -/

/-- The physical pressure source `f - ∇·(u⊗u)` of the recovered velocity. -/
def mildPressureSource (g : SpaceTimeField) (u : ℝ → PeriodicSobolev 3) : SpaceTimeField :=
  fun z ↦ g z - convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2

theorem mildPressureSource_contDiff {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T t : ℝ}
    (hg : ContDiff ℝ ∞ g) (hu : PersistenceInput T u) (ht : t ∈ Ico 0 T) :
    ContDiff ℝ ∞ (fun x ↦ mildPressureSource g u (t, x)) := by
  have hgt : ContDiff ℝ ∞ (fun x : Space ↦ g (t, x)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  exact hgt.sub (convectionDivergenceT_spatial_contDiff
    (persistence_physical_spatial_smooth hu ht))

theorem mildPressureSource_periodic {g : SpaceTimeField} (u : ℝ → PeriodicSobolev 3)
    (hgp : IsPeriodicOn univ g) (t : ℝ) :
    IsPeriodicSpatial (fun x ↦ mildPressureSource g u (t, x)) := by
  intro x l
  have h2 : convectionDivergenceT (torusPhysicalVelocity u) t (x + coordinateVector l) =
      convectionDivergenceT (torusPhysicalVelocity u) t x :=
    convectionDivergenceT_spatial_periodic
      (v := torusPhysicalVelocity u) (t := t)
      (fun y q ↦ torusPhysicalVelocity_periodic u t (mem_univ t) y q) x l
  show g (t, x + coordinateVector l) - convectionDivergenceT (torusPhysicalVelocity u) t
      (x + coordinateVector l) = g (t, x) - convectionDivergenceT (torusPhysicalVelocity u) t x
  rw [hgp t (mem_univ t) x l, h2]

/-- The coefficient pressure: the Leray-complement scalar potential of the
source, with the zero mode set to zero. -/
def mildPressureCoeff (g : SpaceTimeField) (u : ℝ → PeriodicSobolev 3)
    (t : ℝ) (k : PeriodicFrequency) : ℂ :=
  lerayPotentialCoeff (fun x ↦ mildPressureSource g u (t, x)) k

/-- The physical pressure, by scalar Fourier inversion of `mildPressureCoeff`. -/
def mildPressure (g : SpaceTimeField) (u : ℝ → PeriodicSobolev 3) : SpaceTimeScalar :=
  fun z ↦ lerayPotential (fun x ↦ mildPressureSource g u (z.1, x)) z.2

theorem mildPressure_slice (g : SpaceTimeField) (u : ℝ → PeriodicSobolev 3) (t : ℝ) :
    (fun x : Space ↦ mildPressure g u (t, x)) =
      lerayPotential (fun x ↦ mildPressureSource g u (t, x)) := rfl

theorem mildPressure_spatial_contDiff {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T t : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    (ht : t ∈ Ico 0 T) : ContDiff ℝ ∞ (fun x : Space ↦ mildPressure g u (t, x)) := by
  rw [mildPressure_slice]
  exact lerayPotential_contDiff (mildPressureSource_contDiff hg hu ht)
    (mildPressureSource_periodic u hgp t)

/-- Unit spatial periods, on every time set. -/
theorem mildPressure_periodic (g : SpaceTimeField) (u : ℝ → PeriodicSobolev 3) :
    IsPeriodicOn univ (mildPressure g u) :=
  fun t _ x j ↦ lerayPotential_periodic (fun x ↦ mildPressureSource g u (t, x)) x j

/-- The pressure gauge `∫_{T³} p(t) = 0`, on every time set. -/
theorem mildPressure_gauge {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    PressureGaugeT (Ico (0 : ℝ) T) (mildPressure g u) := by
  intro t ht
  show ∫ y : PeriodicTorus, torusLift (fun x ↦ mildPressure g u (t, x)) y
    ∂periodicTorusMeasure = 0
  rw [mildPressure_slice]
  exact lerayPotential_mean (mildPressureSource_contDiff hg hu ht)
    (mildPressureSource_periodic u hgp t)

/-- The `ClassicalSolutionT.pressure_gradient` field. -/
theorem mildPressure_gradient_memLp {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ pressureGradient (mildPressure g u) t x)) 2
        periodicTorusMeasure := by
  intro t ht
  exact memLp_torusLift_vector
    (pressureGradient_continuous (mildPressure_spatial_contDiff hg hgp hu ht)) 2

/-! ## 8. The Poisson equation, the gradient datum, and the force link -/

theorem scalarSpatialLaplacianT_congr {p q : SpaceTimeScalar} {t : ℝ}
    (h : (fun y : Space ↦ p (t, y)) = fun y : Space ↦ q (t, y)) (x : Space) :
    scalarSpatialLaplacianT p t x = scalarSpatialLaplacianT q t x := by
  unfold scalarSpatialLaplacianT
  rw [h]

/-- The `PeriodicLocalRegularity.pressure_poisson` field, in its exact shape. -/
theorem mildPressure_poisson {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      scalarSpatialLaplacianT (mildPressure g u) t x =
        spatialDivergence g t x -
          spatialDivergence (fun z : SpaceTime ↦
            convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x := by
  intro t ht x
  have hS := mildPressureSource_contDiff hg hu ht
  have hSp := mildPressureSource_periodic u hgp t
  have hgt : ContDiff ℝ ∞ (fun y : Space ↦ g (t, y)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  have hct : ContDiff ℝ ∞ (fun y : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t y) :=
    convectionDivergenceT_spatial_contDiff (persistence_physical_spatial_smooth hu ht)
  have hcongr : scalarSpatialLaplacianT (mildPressure g u) t x =
      scalarSpatialLaplacianT
        (fun z : SpaceTime ↦ lerayPotential (fun y ↦ mildPressureSource g u (t, y)) z.2) t x :=
    scalarSpatialLaplacianT_congr (mildPressure_slice g u t) x
  have hdiv1 : spatialDivergence g t x =
      ∑ j : Fin 3, spatialPartial j (fun y : Space ↦ g (t, y) j) x :=
    spatialDivergence_eq_sum hgt x
  have hdiv2 : spatialDivergence (fun z : SpaceTime ↦
      convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x =
      ∑ j : Fin 3, spatialPartial j
        (fun y : Space ↦ convectionDivergenceT (torusPhysicalVelocity u) t y j) x :=
    spatialDivergence_eq_sum (w := fun z : SpaceTime ↦
      convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) hct x
  rw [hcongr, lerayPotential_poisson hS hSp t x, hdiv1, hdiv2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hsrc : (fun y : Space ↦ mildPressureSource g u (t, y) j) =
      fun y : Space ↦ g (t, y) j -
        convectionDivergenceT (torusPhysicalVelocity u) t y j := by
    funext y
    simp only [mildPressureSource, PiLp.sub_apply]
  rw [hsrc]
  exact spatialPartial_sub
    (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hgt).differentiable (by simp) x)
    (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hct).differentiable (by simp) x) j

/-- The gradient of the constructed pressure has exactly the Leray-complement
Fourier data of the source. -/
theorem mildPressure_gradient_coeff {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff
      (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      periodicDerivativeSymbol i k * mildPressureCoeff g u t k := by
  have he : (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) =
      fun x ↦ ((fderiv ℝ (lerayPotential (fun y ↦ mildPressureSource g u (t, y))) x
        (coordinateVector i) : ℝ) : ℂ) := by
    funext x
    rw [pressureGradient_component, mildPressure_slice]
  rw [he]
  exact lerayPotential_gradient_coeff (mildPressureSource_contDiff hg hu ht)
    (mildPressureSource_periodic u hgp t) i k

/-- `∇p` has datum `(I - P)(F - Q)`: the exact T10 Leray complement of any datum
of the source. -/
theorem mildPressure_gradient_leray_complement {g : SpaceTimeField}
    {u : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) {s : ℝ} {B : PeriodicSobolev s}
    (hB : IsPeriodicDatum s (fun x ↦ mildPressureSource g u (t, x)) B)
    {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicFourierCoeff
      (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      torusPhysicalCoeff s B i k -
        ((periodicFrequencyWeight k ^ (-s / 2) : ℝ) : ℂ) * periodicLeray s B i k := by
  rw [mildPressure_gradient_coeff hg hgp hu ht i k]
  exact lerayPotentialCoeff_leray_complement hB hk i

theorem integrable_torusLift_of_continuous_periodic {f : Space → ℂ}
    (hf : Continuous f) (hp : IsPeriodicSpatial f) :
    Integrable (torusLift f) periodicTorusMeasure := by
  have hc : Continuous (torusLift f) :=
    NSFormalization.Paper1.continuous_torusLift hf (fun x j ↦ hp x j)
  simpa using hc.continuousOn.integrableOn_compact (μ := periodicTorusMeasure) isCompact_univ

/-- The source coefficient is exactly `F(t) - Q(u(t),u(t))` at the level of
physical Fourier data: the force datum minus the convection coefficient. -/
theorem mildPressureSourceCoeff_eq_force_sub_convection {g : SpaceTimeField}
    {u : ℝ → PeriodicSobolev 3} {F : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hu : PersistenceInput T u)
    (hF : IsPeriodicSobolevPath 3 g F) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (j : Fin 3) (k : PeriodicFrequency) :
    sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k =
      torusPhysicalCoeff 3 (F t) j k -
        periodicFourierCoeff (fun x ↦
          ((convectionDivergenceT (torusPhysicalVelocity u) t x j : ℝ) : ℂ)) k := by
  have hdat : IsPeriodicDatum 3 (fun x ↦ g (t, x)) (F t) := hF t ht.1
  have hct : ContDiff ℝ ∞ (fun y : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t y) :=
    convectionDivergenceT_spatial_contDiff (persistence_physical_spatial_smooth hu ht)
  have hcp : IsPeriodicSpatial (fun y : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t y) :=
    convectionDivergenceT_spatial_periodic
      (v := torusPhysicalVelocity u) (t := t)
      (fun y q ↦ torusPhysicalVelocity_periodic u t (mem_univ t) y q)
  have h2 : Integrable (torusLift (fun x ↦
      ((convectionDivergenceT (torusPhysicalVelocity u) t x j : ℝ) : ℂ)))
      periodicTorusMeasure :=
    integrable_torusLift_of_continuous_periodic
      (sourceComponent_contDiff hct j).continuous (sourceComponent_periodic hcp j)
  have he : (fun x ↦ ((mildPressureSource g u (t, x) j : ℝ) : ℂ)) =
      fun x ↦ ((g (t, x) j : ℝ) : ℂ) -
        ((convectionDivergenceT (torusPhysicalVelocity u) t x j : ℝ) : ℂ) := by
    funext x
    simp only [mildPressureSource, PiLp.sub_apply, Complex.ofReal_sub]
  rw [sourceComponentCoeff, he,
    periodicFourierCoeff_sub (hdat.integrable_component j) h2 k,
    torusPhysicalCoeff_eq hdat j k]

/-! ## 8b. The periodic convolution theorem and the canonical convection datum -/

/-- A smooth periodic function is its own Fourier series. -/
theorem eq_torusScalarSeries_of_smooth {f : Space → ℂ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) :
    f = torusScalarSeries (periodicFourierCoeff f) := by
  funext x
  rw [periodic_eq_tsum_mFourier hp hs.continuous
    (summable_periodicFourierCoeff_of_smooth hp hs) x]
  refine tsum_congr fun l ↦ ?_
  rw [NSFormalization.Paper1.periodicCharacter, NSFormalization.Paper1.periodicPhase_apply]

theorem torusLift_eq_tsum_mFourier {f : Space → ℂ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (q : PeriodicTorus) :
    torusLift f q = ∑' l, periodicFourierCoeff f l * UnitAddTorus.mFourier l q := by
  conv_lhs => rw [eq_torusScalarSeries_of_smooth hp hs]
  exact torusScalarSeries_lift _ q

/-- **Periodic convolution theorem.** The Fourier coefficients of a pointwise
product are the convolution of the coefficients. -/
theorem periodicFourierCoeff_mul {f g : Space → ℂ}
    (hpf : IsPeriodicSpatial f) (hsf : ContDiff ℝ ∞ f)
    (hpg : IsPeriodicSpatial g) (hsg : ContDiff ℝ ∞ g) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x * g x) k =
      ∑' l, periodicFourierCoeff f l * periodicFourierCoeff g (k - l) := by
  have hfabs : Summable (fun l ↦ ‖periodicFourierCoeff f l‖) := by
    simpa using summable_weight_pow_mul_coeff hpf hsf 0
  have hgc : Continuous (torusLift g) :=
    NSFormalization.Paper1.continuous_torusLift hsg.continuous (fun x j ↦ hpg x j)
  set G : PeriodicFrequency → PeriodicTorus → ℂ := fun l q ↦
    periodicFourierCoeff f l * (UnitAddTorus.mFourier (l - k) q * torusLift g q) with hGdef
  have hint (l : PeriodicFrequency) : Integrable (G l) periodicTorusMeasure := by
    have hc : Continuous (G l) :=
      continuous_const.mul ((UnitAddTorus.mFourier (l - k)).continuous.mul hgc)
    simpa using hc.continuousOn.integrableOn_compact
      (μ := periodicTorusMeasure) isCompact_univ
  have hnorm (l : PeriodicFrequency) (q : PeriodicTorus) :
      ‖G l q‖ = ‖periodicFourierCoeff f l‖ * ‖torusLift g q‖ := by
    simp only [hGdef, norm_mul, torusMFourier_norm, one_mul]
  have hsum : Summable (fun l ↦ ∫ q, ‖G l q‖ ∂periodicTorusMeasure) := by
    have he : (fun l ↦ ∫ q, ‖G l q‖ ∂periodicTorusMeasure) =
        fun l ↦ ‖periodicFourierCoeff f l‖ *
          ∫ q, ‖torusLift g q‖ ∂periodicTorusMeasure := by
      funext l
      simp_rw [hnorm l]
      exact integral_const_mul _ _
    rw [he]
    exact hfabs.mul_right _
  have hlift (q : PeriodicTorus) :
      UnitAddTorus.mFourier (-k) q • torusLift (fun x ↦ f x * g x) q = ∑' l, G l q := by
    have he : torusLift (fun x ↦ f x * g x) q = torusLift f q * torusLift g q := rfl
    rw [he, torusLift_eq_tsum_mFourier hpf hsf q, smul_eq_mul, ← tsum_mul_right,
      ← tsum_mul_left]
    refine tsum_congr fun l ↦ ?_
    simp only [hGdef, sub_eq_add_neg, UnitAddTorus.mFourier_add]
    ring
  change (∫ q, UnitAddTorus.mFourier (-k) q •
    torusLift (fun x ↦ f x * g x) q ∂periodicTorusMeasure) = _
  simp_rw [hlift]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun l ↦ ?_
  rw [hGdef, integral_const_mul]
  congr 1
  change _ = ∫ q, UnitAddTorus.mFourier (-(k - l)) q • torusLift g q ∂periodicTorusMeasure
  simp only [neg_sub, smul_eq_mul]

theorem euclidean_sum_apply {ι : Type*} (s : Finset ι) (w : ι → Space) (i : Fin 3) :
    (∑ j ∈ s, w j) i = ∑ j ∈ s, (w j) i :=
  map_sum (EuclideanSpace.proj (𝕜 := ℝ) i) w s

/-- The `i`-th component of the tensor divergence, as a sum of scalar
derivatives of products. -/
theorem convectionDivergenceT_component {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x))) (x : Space) (i : Fin 3) :
    convectionDivergenceT v t x i =
      ∑ j : Fin 3, spatialPartial j (fun y : Space ↦ v (t, y) j * v (t, y) i) x := by
  show (∑ j : Fin 3, fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x
    (coordinateVector j)) i = _
  rw [euclidean_sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hprod : ContDiff ℝ ∞ (fun y : Space ↦ (v (t, y) j) • v (t, y)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hv).smul hv
  have h : HasFDerivAt (fun y : Space ↦ (v (t, y) j) * (v (t, y) i))
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp
        (fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
      ((hprod.differentiable (by simp) x).hasFDerivAt)
  show (fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x (coordinateVector j)) i =
    fderiv ℝ (fun y : Space ↦ v (t, y) j * v (t, y) i) x (coordinateVector j)
  rw [h.fderiv]
  rfl

/-- Fourier coefficients of a finite sum of scalar coordinate derivatives. -/
theorem periodicFourierCoeff_sum_spatialPartial {h : Fin 3 → Space → ℝ}
    (hs : ∀ j, ContDiff ℝ ∞ (h j)) (hp : ∀ j, IsPeriodicSpatial (h j))
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((∑ j : Fin 3, spatialPartial j (h j) x : ℝ) : ℂ)) k =
      ∑ j : Fin 3, periodicDerivativeSymbol j k *
        periodicFourierCoeff (fun x ↦ ((h j x : ℝ) : ℂ)) k := by
  have hjc (j : Fin 3) : ContDiff ℝ ∞ (fun x ↦ ((h j x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hs j)
  have hjp (j : Fin 3) : IsPeriodicSpatial (fun x ↦ ((h j x : ℝ) : ℂ)) :=
    fun x l ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (hp j x l)
  have hds (j : Fin 3) : ContDiff ℝ ∞ (spatialPartial j (fun x ↦ ((h j x : ℝ) : ℂ))) :=
    ((hjc j).fderiv_right (by simp)).clm_apply contDiff_const
  have hcomplex : (fun x ↦ ((∑ j : Fin 3, spatialPartial j (h j) x : ℝ) : ℂ)) =
      fun x ↦ ∑ j : Fin 3, spatialPartial j (fun y ↦ ((h j y : ℝ) : ℂ)) x := by
    funext x
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h1 : ContDiff ℝ 1 (h j) := (hs j).of_le (by simp)
    rw [spatialPartial_complexify h1 j]
  rw [hcomplex]
  have he : periodicFourierCoeff (fun x ↦ ∑ j : Fin 3,
      spatialPartial j (fun y ↦ ((h j y : ℝ) : ℂ)) x) k =
        ∑ j : Fin 3, periodicFourierCoeff (spatialPartial j (fun y ↦ ((h j y : ℝ) : ℂ))) k := by
    simp only [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff_eq_cube,
      Finset.mul_sum, NavierStokes.PeriodicIntegration.cubeIntegral]
    apply integral_finsetSum
    intro j _
    exact NavierStokes.PeriodicIntegration.integrable_cube
      ((NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous.mul (hds j).continuous)
  rw [he]
  exact Finset.sum_congr rfl fun j _ ↦
    periodicFourierCoeff_fderiv (hjp j) ((hjc j).of_le (by simp)) j k

/-- The canonical unprojected convection datum of `ConvolutionBound.lean`, read
off in unweighted physical coefficients. -/
theorem torusPhysicalCoeff_torusConvectionDatum (A B : PeriodicSobolev 3)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusPhysicalCoeff 2 (torusConvectionDatum A B) i k =
      ∑ j : Fin 3, periodicDerivativeSymbol j k *
        ∑' l, torusPhysicalCoeff 3 A j l * torusPhysicalCoeff 3 B i (k - l) := by
  have hW : 0 < periodicFrequencyWeight k := mildPressure_weight_pos k
  have hinv : periodicFrequencyWeight k ^ (-(2 : ℝ) / 2) = (periodicFrequencyWeight k)⁻¹ := by
    rw [show (-(2 : ℝ) / 2) = -(1 : ℝ) by norm_num, Real.rpow_neg hW.le, Real.rpow_one]
  have hcancel : ((periodicFrequencyWeight k ^ (-(2 : ℝ) / 2) : ℝ) : ℂ) *
      (periodicFrequencyWeight k : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hinv, inv_mul_cancel₀ hW.ne', Complex.ofReal_one]
  rw [torusPhysicalCoeff, torusConvectionDatum_coeff, torusConvectionSymbol, ← mul_assoc,
    hcancel, one_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  exact tsum_congr fun l ↦ by simp only [torusPhysicalCoeff]; ring

/-- The physical convection coefficient **is** the canonical unprojected
convection datum of `ConvolutionBound.lean`, via the convolution theorem. -/
theorem periodicFourierCoeff_convection_eq_torusConvectionDatum
    {u : ℝ → PeriodicSobolev 3} {T t : ℝ} (hu : PersistenceInput T u)
    (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff
      (fun x ↦ ((convectionDivergenceT (torusPhysicalVelocity u) t x i : ℝ) : ℂ)) k =
      torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) i k := by
  have hv : ContDiff ℝ ∞ (fun x : Space ↦ torusPhysicalVelocity u (t, x)) :=
    persistence_physical_spatial_smooth hu ht
  have hvp : IsPeriodicSpatial (fun x : Space ↦ torusPhysicalVelocity u (t, x)) :=
    fun y q ↦ torusPhysicalVelocity_periodic u t (mem_univ t) y q
  have hcomp (j : Fin 3) :
      ContDiff ℝ ∞ (fun x ↦ ((torusPhysicalVelocity u (t, x) j : ℝ) : ℂ)) :=
    sourceComponent_contDiff hv j
  have hcompp (j : Fin 3) :
      IsPeriodicSpatial (fun x ↦ ((torusPhysicalVelocity u (t, x) j : ℝ) : ℂ)) :=
    sourceComponent_periodic hvp j
  have hcoeff (j : Fin 3) (l : PeriodicFrequency) :
      periodicFourierCoeff (fun x ↦ ((torusPhysicalVelocity u (t, x) j : ℝ) : ℂ)) l =
        torusPhysicalCoeff 3 (u t) j l :=
    (torusPhysicalCoeff_eq (torusPhysicalField_datum (u t)) j l).symm
  have hHs : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space ↦
      torusPhysicalVelocity u (t, y) j * torusPhysicalVelocity u (t, y) i) := fun j ↦
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hv).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hv)
  have hHp : ∀ j : Fin 3, IsPeriodicSpatial (fun y : Space ↦
      torusPhysicalVelocity u (t, y) j * torusPhysicalVelocity u (t, y) i) := fun j y l ↦
    congrArg (fun w : Space ↦ (w j) * (w i)) (hvp y l)
  have hfun : (fun x ↦ ((convectionDivergenceT (torusPhysicalVelocity u) t x i : ℝ) : ℂ)) =
      fun x ↦ ((∑ j : Fin 3, spatialPartial j
        (fun y : Space ↦ torusPhysicalVelocity u (t, y) j *
          torusPhysicalVelocity u (t, y) i) x : ℝ) : ℂ) := by
    funext x
    rw [convectionDivergenceT_component hv x i]
  rw [hfun, periodicFourierCoeff_sum_spatialPartial hHs hHp k,
    torusPhysicalCoeff_torusConvectionDatum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  have he : (fun x ↦ ((torusPhysicalVelocity u (t, x) j *
      torusPhysicalVelocity u (t, x) i : ℝ) : ℂ)) =
      fun x ↦ ((torusPhysicalVelocity u (t, x) j : ℝ) : ℂ) *
        ((torusPhysicalVelocity u (t, x) i : ℝ) : ℂ) := by
    funext x
    rw [Complex.ofReal_mul]
  rw [he, periodicFourierCoeff_mul (hcompp j) (hcomp j) (hcompp i) (hcomp i) k]
  exact tsum_congr fun l ↦ by rw [hcoeff j l, hcoeff i (k - l)]

/-- Hence the canonical convection datum really is the order-two Fourier datum
of the physical tensor divergence. -/
theorem torusConvectionDatum_isPeriodicDatum
    {u : ℝ → PeriodicSobolev 3} {T t : ℝ} (hu : PersistenceInput T u)
    (ht : t ∈ Ico (0 : ℝ) T) :
    IsPeriodicDatum 2 (fun x ↦ convectionDivergenceT (torusPhysicalVelocity u) t x)
      (torusConvectionDatum (u t) (u t)) := by
  have hv : ContDiff ℝ ∞ (fun x : Space ↦ torusPhysicalVelocity u (t, x)) :=
    persistence_physical_spatial_smooth hu ht
  have hvp : IsPeriodicSpatial (fun x : Space ↦ torusPhysicalVelocity u (t, x)) :=
    fun y q ↦ torusPhysicalVelocity_periodic u t (mem_univ t) y q
  have hct : ContDiff ℝ ∞ (fun x : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t x) :=
    convectionDivergenceT_spatial_contDiff hv
  have hcp : IsPeriodicSpatial (fun x : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t x) :=
    convectionDivergenceT_spatial_periodic (v := torusPhysicalVelocity u) (t := t) hvp
  refine ⟨hcp, (memLp_torusLift_vector hct.continuous 1).integrable (by norm_num), ?_⟩
  intro i k
  have hW : 0 < periodicFrequencyWeight k := mildPressure_weight_pos k
  have hbridge := periodicFourierCoeff_convection_eq_torusConvectionDatum hu ht i k
  simp only [torusPhysicalCoeff] at hbridge
  show (torusConvectionDatum (u t) (u t)).1 i k =
    (periodicFrequencyWeight k ^ ((2 : ℝ) / 2)) • periodicFourierCoeff
      (fun x ↦ ((convectionDivergenceT (torusPhysicalVelocity u) t x i : ℝ) : ℂ)) k
  rw [hbridge, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add hW, show (2 : ℝ) / 2 + -(2 : ℝ) / 2 = 0 by norm_num,
    Real.rpow_zero, Complex.ofReal_one, one_mul]

/-! ## 8c. Canonical `F - Q` coefficients, and every-`H^m` membership -/

/-- The source coefficient is the canonical coefficient-side `F - Q`. -/
theorem mildPressureSourceCoeff_eq_canonical {g : SpaceTimeField}
    {u : ℝ → PeriodicSobolev 3} {F : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hu : PersistenceInput T u) (hF : IsPeriodicSobolevPath 3 g F)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (j : Fin 3) (k : PeriodicFrequency) :
    sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k =
      torusPhysicalCoeff 3 (F t) j k -
        torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) j k := by
  rw [mildPressureSourceCoeff_eq_force_sub_convection hu hF ht j k,
    periodicFourierCoeff_convection_eq_torusConvectionDatum hu ht j k]

/-- `∇p = (I - P)(F - Q)` written out in canonical coefficient data. -/
theorem mildPressure_gradient_canonical {g : SpaceTimeField}
    {u : ℝ → PeriodicSobolev 3} {F : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    (hF : IsPeriodicSobolevPath 3 g F) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicFourierCoeff
      (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∑ j : Fin 3, (k j : ℂ) *
          (torusPhysicalCoeff 3 (F t) j k -
            torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) j k) := by
  rw [mildPressure_gradient_coeff hg hgp hu ht i k,
    show mildPressureCoeff g u t k =
      lerayPotentialCoeff (fun x ↦ mildPressureSource g u (t, x)) k from rfl,
    periodicDerivativeSymbol_mul_lerayPotentialCoeff _ hk i]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [mildPressureSourceCoeff_eq_canonical hu hF ht j k]

/-- The canonical order-two datum of the source is literally `G₂ - Q`. -/
theorem mildPressureSource_canonical_datum {g : SpaceTimeField}
    {u : ℝ → PeriodicSobolev 3} {T : ℝ} (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) {G₂ : PeriodicSobolev 2}
    (hG : IsPeriodicDatum 2 (fun x : Space ↦ g (t, x)) G₂) :
    IsPeriodicDatum 2 (fun x ↦ mildPressureSource g u (t, x))
      (G₂ - torusConvectionDatum (u t) (u t)) :=
  datum_sub hG (torusConvectionDatum_isPeriodicDatum hu ht)

theorem mildPressureSource_exists_canonical_datum {g : SpaceTimeField}
    {u : ℝ → PeriodicSobolev 3} {T : ℝ} (hg : ContDiff ℝ ∞ g)
    (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ G₂ : PeriodicSobolev 2, IsPeriodicDatum 2 (fun x : Space ↦ g (t, x)) G₂ ∧
      IsPeriodicDatum 2 (fun x ↦ mildPressureSource g u (t, x))
        (G₂ - torusConvectionDatum (u t) (u t)) := by
  obtain ⟨G₂, hG⟩ := smooth_periodic_datum 2 (hg.comp (contDiff_const.prodMk contDiff_id))
    (fun x j ↦ hgp t (mem_univ t) x j)
  exact ⟨G₂, hG, mildPressureSource_canonical_datum hu ht hG⟩

/-- The gradient datum is the T10 Leray complement of the canonical `F - Q`. -/
theorem mildPressure_gradient_leray_canonical {g : SpaceTimeField}
    {u : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) {G₂ : PeriodicSobolev 2}
    (hG : IsPeriodicDatum 2 (fun x : Space ↦ g (t, x)) G₂)
    {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicFourierCoeff
      (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      torusPhysicalCoeff 2 (G₂ - torusConvectionDatum (u t) (u t)) i k -
        ((periodicFrequencyWeight k ^ (-(2 : ℝ) / 2) : ℝ) : ℂ) *
          periodicLeray 2 (G₂ - torusConvectionDatum (u t) (u t)) i k :=
  mildPressure_gradient_leray_complement hg hgp hu ht
    (mildPressureSource_canonical_datum hu ht hG) hk i

/-- The pressure slice has an explicit scalar Sobolev datum at every real order:
the order-`s` weighted coefficient family. -/
theorem scalar_datum_of_smooth {z : Space → ℝ} (hs : ContDiff ℝ ∞ z)
    (hp : IsPeriodicSpatial z) (s : ℝ) :
    ∃ A : PeriodicScalarData,
      NSFormalization.Section3.T12.IsPeriodicScalarDatum s z A ∧
        ∀ k, A k = (periodicFrequencyWeight k ^ (s / 2) : ℝ) •
          periodicFourierCoeff (fun x ↦ ((z x : ℝ) : ℂ)) k := by
  have hc : ContDiff ℝ ∞ (fun x ↦ ((z x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  have hpc : NavierStokes.PeriodicIntegration.UnitPeriods (fun x ↦ ((z x : ℝ) : ℂ)) :=
    fun x j ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (hp x j)
  refine ⟨NSFormalization.Paper1.smoothPeriodicWeightedFourierLp s
    (fun x ↦ ((z x : ℝ) : ℂ)) hc hpc, ⟨hp, ?_, ?_⟩, ?_⟩
  · exact ((NSFormalization.Paper1.memLp_torusLift hc.continuous 1).re).integrable (by norm_num)
  · intro k
    simp only [NSFormalization.Paper1.smoothPeriodicWeightedFourierLp,
      periodicFrequencyWeight_eq_paper1]
  · intro k
    simp only [NSFormalization.Paper1.smoothPeriodicWeightedFourierLp,
      periodicFrequencyWeight_eq_paper1]

/-- Every smooth periodic scalar lies in every canonical periodic `H^m`. -/
theorem memPeriodicHmScalar_of_smooth {z : Space → ℝ} (hs : ContDiff ℝ ∞ z)
    (hp : IsPeriodicSpatial z) (m : ℕ) :
    NSFormalization.Section3.T12.MemPeriodicHmScalar m z := by
  obtain ⟨A, hA, _⟩ := scalar_datum_of_smooth hs hp (m : ℝ)
  have hc : ContDiff ℝ ∞ (fun x ↦ ((z x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  refine ⟨hp, (NSFormalization.Paper1.memLp_torusLift hc.continuous 2).re, ?_⟩
  exact ne_top_of_le_ne_top (by simp)
    (iInf_le (fun A : {A : PeriodicScalarData //
      NSFormalization.Section3.T12.IsPeriodicScalarDatum (m : ℝ) z A} ↦ ‖A.1‖ₑ) ⟨A, hA⟩)

theorem mildPressure_coeff {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((mildPressure g u (t, x) : ℝ) : ℂ)) k =
      mildPressureCoeff g u t k := by
  have he : (fun x : Space ↦ ((mildPressure g u (t, x) : ℝ) : ℂ)) =
      fun x : Space ↦
        ((lerayPotential (fun y ↦ mildPressureSource g u (t, y)) x : ℝ) : ℂ) :=
    congrArg (fun f : Space → ℝ ↦ fun x : Space ↦ ((f x : ℝ) : ℂ)) (mildPressure_slice g u t)
  rw [he]
  exact lerayPotential_coeff (mildPressureSource_contDiff hg hu ht)
    (mildPressureSource_periodic u hgp t) k

/-- **The coefficient pressure is in every `H^m`**: at each time the order-`m`
weighted family `W(k)^{m/2} p̂(t)(k)` is the canonical scalar `H^m` datum of the
pressure slice. -/
theorem mildPressure_scalar_datum {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3}
    {T : ℝ} (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hu : PersistenceInput T u) (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ A : PeriodicScalarData,
      NSFormalization.Section3.T12.IsPeriodicScalarDatum (m : ℝ)
        (fun x : Space ↦ mildPressure g u (t, x)) A ∧
        ∀ k, A k = (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) •
          mildPressureCoeff g u t k := by
  obtain ⟨A, hA, hcoeff⟩ := scalar_datum_of_smooth
    (mildPressure_spatial_contDiff hg hgp hu ht)
    (fun x j ↦ mildPressure_periodic g u t (mem_univ t) x j) (m : ℝ)
  exact ⟨A, hA, fun k ↦ by rw [hcoeff k, mildPressure_coeff hg hgp hu ht k]⟩

/-- Consequently every pressure slice lies in every periodic `H^m(T³)`. -/
theorem mildPressure_memPeriodicHm {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3}
    {T : ℝ} (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hu : PersistenceInput T u) (m : ℕ) :
    ∀ t ∈ Ico (0 : ℝ) T, NSFormalization.Section3.T12.MemPeriodicHmScalar m
      (fun x : Space ↦ mildPressure g u (t, x)) := fun t ht ↦
  memPeriodicHmScalar_of_smooth (mildPressure_spatial_contDiff hg hgp hu ht)
    (fun x j ↦ mildPressure_periodic g u t (mem_univ t) x j) m

/-! ## 9. The bundled pressure fields -/

/-- Every pressure clause of `ClassicalSolutionT` / `PeriodicLocalRegularity`
that this lane proves, bundled for the assembly lane.  This is a *conclusion*:
`mildPressure_fields` builds it from `PersistenceInput` and the smoothness and
periodicity of the physical force alone. -/
structure MildPressureFields (g : SpaceTimeField) (u : ℝ → PeriodicSobolev 3) (T : ℝ) :
    Prop where
  spatial_smooth : ∀ t ∈ Ico (0 : ℝ) T,
    ContDiff ℝ ∞ (fun x : Space ↦ mildPressure g u (t, x))
  periodic : IsPeriodicOn (Ico (0 : ℝ) T) (mildPressure g u)
  gauge : PressureGaugeT (Ico (0 : ℝ) T) (mildPressure g u)
  gradient_memLp : ∀ t ∈ Ico (0 : ℝ) T,
    MemLp (torusLift (fun x ↦ pressureGradient (mildPressure g u) t x)) 2 periodicTorusMeasure
  gradient_coeff : ∀ t ∈ Ico (0 : ℝ) T, ∀ (i : Fin 3) (k : PeriodicFrequency),
    periodicFourierCoeff (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      periodicDerivativeSymbol i k * mildPressureCoeff g u t k
  coeff : ∀ t ∈ Ico (0 : ℝ) T, ∀ k : PeriodicFrequency,
    periodicFourierCoeff (fun x ↦ ((mildPressure g u (t, x) : ℝ) : ℂ)) k =
      mildPressureCoeff g u t k
  memHm : ∀ m : ℕ, ∀ t ∈ Ico (0 : ℝ) T,
    NSFormalization.Section3.T12.MemPeriodicHmScalar m
      (fun x : Space ↦ mildPressure g u (t, x))
  scalar_datum : ∀ m : ℕ, ∀ t ∈ Ico (0 : ℝ) T,
    ∃ A : PeriodicScalarData,
      NSFormalization.Section3.T12.IsPeriodicScalarDatum (m : ℝ)
        (fun x : Space ↦ mildPressure g u (t, x)) A ∧
        ∀ k, A k = (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) •
          mildPressureCoeff g u t k
  poisson : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    scalarSpatialLaplacianT (mildPressure g u) t x =
      spatialDivergence g t x -
        spatialDivergence (fun z : SpaceTime ↦
          convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x

theorem mildPressure_fields {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    MildPressureFields g u T where
  spatial_smooth := fun _ ht ↦ mildPressure_spatial_contDiff hg hgp hu ht
  periodic := fun t _ x j ↦ mildPressure_periodic g u t (mem_univ t) x j
  gauge := mildPressure_gauge hg hgp hu
  gradient_memLp := mildPressure_gradient_memLp hg hgp hu
  gradient_coeff := fun _ ht i k ↦ mildPressure_gradient_coeff hg hgp hu ht i k
  coeff := fun _ ht k ↦ mildPressure_coeff hg hgp hu ht k
  memHm := fun m ↦ mildPressure_memPeriodicHm hg hgp hu m
  scalar_datum := fun m _ ht ↦ mildPressure_scalar_datum hg hgp hu m ht
  poisson := mildPressure_poisson hg hgp hu

/-! ## 10. Non-vacuity: the construction produces a nonzero pressure -/

/-- A single real Fourier mode, as a finitely supported coefficient family. -/
def testPressureSourceCoeff (m : PeriodicFrequency) (l : PeriodicFrequency) : ℂ :=
  (if l = m then 1 else 0) + (if l = -m then 1 else 0)

theorem testPressureSourceCoeff_neg (m l : PeriodicFrequency) :
    testPressureSourceCoeff m (-l) = star (testPressureSourceCoeff m l) := by
  simp only [testPressureSourceCoeff, star_add, apply_ite (star : ℂ → ℂ), star_one, star_zero,
    neg_eq_iff_eq_neg]
  ring_nf

theorem testPressureSourceCoeff_summable (m : PeriodicFrequency) (N : ℕ) :
    Summable (fun l ↦ periodicFrequencyWeight l ^ N * ‖testPressureSourceCoeff m l‖) := by
  classical
  apply summable_of_ne_finset_zero (s := ({m, -m} : Finset PeriodicFrequency))
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  simp [testPressureSourceCoeff, hl.1, hl.2]

/-- A smooth periodic vector field carrying exactly one real Fourier mode. -/
def testPressureSource (m : PeriodicFrequency) : SpatialField :=
  fun x ↦ WithLp.toLp 2 (fun i ↦
    if i = 0 then (torusScalarSeries (testPressureSourceCoeff m) x).re else 0)

theorem testPressureSource_contDiff (m : PeriodicFrequency) :
    ContDiff ℝ ∞ (testPressureSource m) := by
  apply (PiLp.contDiff_toLp (p := 2)).comp
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · subst hi
    simp only [↓reduceIte]
    exact Complex.reCLM.contDiff.comp
      (torusScalarSeries_contDiff (testPressureSourceCoeff_summable m))
  · simp only [hi, ↓reduceIte]
    exact contDiff_const

theorem testPressureSource_periodic (m : PeriodicFrequency) :
    IsPeriodicSpatial (testPressureSource m) := by
  intro x j
  apply WithLp.ofLp_injective 2
  funext i
  change (if i = 0 then (torusScalarSeries (testPressureSourceCoeff m)
      (x + coordinateVector j)).re else 0) =
    (if i = 0 then (torusScalarSeries (testPressureSourceCoeff m) x).re else 0)
  rw [torusScalarSeries_periodic (testPressureSourceCoeff m) x j]

theorem testPressureSource_coeff (m : PeriodicFrequency) (j : Fin 3) (k : PeriodicFrequency) :
    sourceComponentCoeff (testPressureSource m) j k =
      if j = 0 then testPressureSourceCoeff m k else 0 := by
  by_cases hj : j = 0
  · subst hj
    have he : (fun x ↦ ((testPressureSource m x 0 : ℝ) : ℂ)) =
        torusScalarSeries (testPressureSourceCoeff m) := by
      funext x
      change ((torusScalarSeries (testPressureSourceCoeff m) x).re : ℂ) = _
      exact Complex.conj_eq_iff_re.mp
        (torusScalarSeries_conj (testPressureSourceCoeff_neg m) x)
    have hsum : Summable (fun l ↦ ‖testPressureSourceCoeff m l‖) := by
      simpa using testPressureSourceCoeff_summable m 0
    rw [sourceComponentCoeff, he, torusScalarSeries_coeff hsum k]
    simp
  · have he : (fun x ↦ ((testPressureSource m x j : ℝ) : ℂ)) = fun _ ↦ (0 : ℂ) := by
      funext x
      change (((if j = 0 then (torusScalarSeries (testPressureSourceCoeff m) x).re
        else 0) : ℝ) : ℂ) = 0
      rw [ite_eq_right (fun hc ↦ absurd hc hj), Complex.ofReal_zero]
    rw [sourceComponentCoeff, he, periodicFourierCoeff_const]
    simp [hj]

/-- The pressure coefficient of the one-mode source is nonzero at that mode.
The concrete lattice mode is supplied by the caller, so that every declaration
of this module has the standard three transitive axioms. -/
theorem lerayPotentialCoeff_testPressureSource_ne_zero {m : PeriodicFrequency}
    (hm : m ≠ 0) (hneg : ¬ m = -m) (hm0 : m 0 ≠ 0) :
    lerayPotentialCoeff (testPressureSource m) m ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDpos : 0 < ∑ j : Fin 3, (m j : ℝ) ^ 2 :=
    lt_of_lt_of_le one_pos (mildPressure_one_le_sq_sum hm)
  have hnum : (∑ j : Fin 3, (m j : ℂ) *
      sourceComponentCoeff (testPressureSource m) j m) = (m 0 : ℂ) := by
    simp only [testPressureSource_coeff, testPressureSourceCoeff, ↓reduceIte, hneg]
    simp
  have hE : (2 * Real.pi * Complex.I) * ((∑ j : Fin 3, (m j : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hDpos.ne')
  simp only [lerayPotentialCoeff, hm, ↓reduceIte, hnum]
  exact div_ne_zero (Int.cast_ne_zero.mpr hm0) hE

/-- The constructed physical potential of that source is not the zero field. -/
theorem lerayPotential_testPressureSource_ne_zero {m : PeriodicFrequency}
    (hm : m ≠ 0) (hneg : ¬ m = -m) (hm0 : m 0 ≠ 0) :
    lerayPotential (testPressureSource m) ≠ 0 := by
  intro h
  apply lerayPotentialCoeff_testPressureSource_ne_zero hm hneg hm0
  rw [← lerayPotential_coeff (testPressureSource_contDiff m)
    (testPressureSource_periodic m) m]
  have he : (fun x ↦ ((lerayPotential (testPressureSource m) x : ℝ) : ℂ)) =
      fun _ ↦ (0 : ℂ) := by
    funext x
    have hx : lerayPotential (testPressureSource m) x = 0 := congrFun h x
    rw [hx, Complex.ofReal_zero]
  rw [he, periodicFourierCoeff_const]
  simp

/-! ## 11. A concrete nonzero instance of the whole construction -/

theorem convectionDivergenceT_of_constant_slice {v : SpaceTimeField} {t : ℝ} {c : Space}
    (hv : ∀ x : Space, v (t, x) = c) (x : Space) : convectionDivergenceT v t x = 0 := by
  have hconst (j : Fin 3) : (fun y : Space ↦ (v (t, y) j) • v (t, y)) =
      fun _ : Space ↦ (c j) • c := by
    funext y
    rw [hv y]
  show (∑ j : Fin 3, fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x
    (coordinateVector j)) = 0
  simp [hconst]

theorem torusPhysicalVelocity_constant_slice (c : Space) (t : ℝ) (x : Space) :
    torusPhysicalVelocity (fun r : ℝ ↦ (1 + r) • torusConstantDatum 3 c) (t, x) = (1 + t) • c := by
  change torusPhysicalField ((1 + t) • torusConstantDatum 3 c) x = (1 + t) • c
  rw [torusPhysicalField_eq continuous_const (torusConstantDatum_smul 3 (1 + t) c)]

/-- With a spatially constant velocity the pressure is the potential of the force. -/
theorem mildPressure_constant_velocity (g : SpaceTimeField) (c : Space) (t : ℝ) :
    (fun x : Space ↦ mildPressure g (fun r : ℝ ↦ (1 + r) • torusConstantDatum 3 c) (t, x)) =
      lerayPotential (fun x ↦ g (t, x)) := by
  rw [mildPressure_slice]
  congr 1
  funext x
  show g (t, x) - convectionDivergenceT
    (torusPhysicalVelocity (fun r : ℝ ↦ (1 + r) • torusConstantDatum 3 c)) t x = g (t, x)
  rw [convectionDivergenceT_of_constant_slice
    (c := (1 + t) • c) (torusPhysicalVelocity_constant_slice c t) x, sub_zero]

/-- All delivered pressure fields hold for a genuine persistent coefficient path
driven by a nonconstant smooth periodic force, and the resulting pressure is not
the zero field.  The concrete lattice mode is a parameter; a witness for the
three hypotheses is exhibited in `probes/mild_pressure_closes.lean`. -/
theorem mildPressure_nonzero_instance {m : PeriodicFrequency}
    (hm : m ≠ 0) (hneg : ¬ m = -m) (hm0 : m 0 ≠ 0) (c : Space) :
    MildPressureFields (fun z : SpaceTime ↦ testPressureSource m z.2)
        (fun t : ℝ ↦ (1 + t) • torusConstantDatum 3 c) 1 ∧
      (fun x : Space ↦ mildPressure (fun z : SpaceTime ↦ testPressureSource m z.2)
        (fun t : ℝ ↦ (1 + t) • torusConstantDatum 3 c) (0, x)) ≠ 0 := by
  refine ⟨mildPressure_fields
    ((testPressureSource_contDiff m).comp contDiff_snd)
    (fun t _ x j ↦ testPressureSource_periodic m x j)
    (persistence_affine_constant 1 c), ?_⟩
  rw [mildPressure_constant_velocity]
  exact lerayPotential_testPressureSource_ne_zero hm hneg hm0

end NSFormalization.Section3.T11
