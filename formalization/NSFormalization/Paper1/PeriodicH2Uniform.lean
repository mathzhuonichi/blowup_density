import NSFormalization.Paper1.PeriodicH2Embedding
import NSFormalization.Paper1.FourierReconstructionAdapter
import NSFormalization.Paper1.PeriodicHigherSobolev

/-!
# Absolute Fourier summability from weighted H² data

This file combines the proved inverse Bessel lattice series with the actual
second-derivative Fourier energy. It obtains absolute coefficient summability
from `C²` periodicity, then uses Fourier reconstruction and finite-frequency
Cauchy--Schwarz to prove the `H²` bound for the uniform norm.
-/

noncomputable section

open scoped BigOperators
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

namespace NSFormalization.Paper1

theorem summable_norm_of_periodicH2_weighted
    (c : PeriodicFrequency → ℂ)
    (hW : Summable (fun k => periodicH2Weight k * ‖c k‖ ^ 2))
    (hI : Summable (fun k => periodicH2InverseWeight k)) :
    Summable (fun k => ‖c k‖) := by
  have hsum : Summable (fun k =>
      (1 / 2 : ℝ) * (periodicH2Weight k * ‖c k‖ ^ 2 +
        periodicH2InverseWeight k)) :=
    (hW.add hI).mul_left (1 / 2 : ℝ)
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg (c k)) ?_ hsum
  intro k
  let a : ℝ := Real.sqrt (periodicH2Weight k) * ‖c k‖
  let b : ℝ := Real.sqrt (periodicH2InverseWeight k)
  have ha : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hab : a * b = ‖c k‖ := by
    dsimp [a, b]
    calc
      Real.sqrt (periodicH2Weight k) * ‖c k‖ *
          Real.sqrt (periodicH2InverseWeight k) =
          (Real.sqrt (periodicH2Weight k) *
            Real.sqrt (periodicH2InverseWeight k)) * ‖c k‖ := by ring
      _ = ‖c k‖ := by
        rw [← Real.sqrt_mul (periodicH2Weight_pos k).le]
        rw [periodicH2Weight_mul_inverse, Real.sqrt_one, one_mul]
  have hsq_a : a ^ 2 = periodicH2Weight k * ‖c k‖ ^ 2 := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (periodicH2Weight_pos k).le]
  have hsq_b : b ^ 2 = periodicH2InverseWeight k := by
    dsimp [b]
    exact Real.sq_sqrt (inv_nonneg.mpr (periodicH2Weight_pos k).le)
  have hAMGM := two_mul_le_add_sq a b
  nlinarith

theorem summable_periodicFourierCoeff_of_h2
    {f : Space → ℂ} (hf : ContDiff ℝ 2 f) (hp : UnitPeriods f)
    (hI : Summable (fun k => periodicH2InverseWeight k)) :
    Summable (periodicFourierCoeff f) := by
  apply Summable.of_norm
  exact summable_norm_of_periodicH2_weighted
    (fun k => periodicFourierCoeff f k)
    (summable_periodicSobolev_two hf hp) hI

/-- Concrete `C²` version: the inverse Bessel series is discharged by the
  lattice comparison proved in `PeriodicH2Embedding`. -/
theorem summable_periodicFourierCoeff_of_h2_actual
    {f : Space → ℂ} (hf : ContDiff ℝ 2 f) (hp : UnitPeriods f) :
    Summable (periodicFourierCoeff f) := by
  exact summable_periodicFourierCoeff_of_h2 hf hp
    summable_periodicH2InverseWeight

/-- The universal three-dimensional `H²` to uniform-norm constant in the
  actual unit-period Fourier convention. -/
def periodicH2UniformConstant : ℝ :=
  Real.sqrt (∑' k : PeriodicFrequency, periodicH2InverseWeight k)

/-- Every physical point of a `C²` periodic field satisfies the genuine
  Bessel `H²` bound. The coefficient summability is proved above. -/
theorem norm_le_periodicH2UniformConstant_mul
    {f : Space → ℂ} (hf : ContDiff ℝ 2 f) (hp : UnitPeriods f) (x : Space) :
    ‖f x‖ ≤ periodicSobolevNorm 2 f * periodicH2UniformConstant := by
  have hc := summable_periodicFourierCoeff_of_h2_actual hf hp
  have hmode (k : PeriodicFrequency) : ‖periodicCharacter k x‖ = 1 := by
    rw [periodicCharacter_eq_mFourier]
    change ‖∏ i : Fin 3, fourier (k i) (x i : UnitAddCircle)‖ = 1
    simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]
  have henergy : 0 ≤ periodicSobolevSq 2 f := by
    exact tsum_nonneg (fun k => mul_nonneg (periodicH2Weight_pos k).le (sq_nonneg _))
  apply le_of_tendsto' (tendsto_periodicFourier_partialSums hf.continuous hp hc x).norm
  intro S
  apply finite_fourier_sum_h2_bound_of_summable_inverse
    (fun k => periodicCharacter k x * periodicFourierCoeff f k) S
    (E := periodicSobolevNorm 2 f) ?_ (Real.sqrt_nonneg _)
    summable_periodicH2InverseWeight
  simp only [norm_mul, hmode, one_mul]
  change (∑ k ∈ S, periodicH2Weight k * ‖periodicFourierCoeff f k‖ ^ 2) ≤
    (Real.sqrt (periodicSobolevSq 2 f)) ^ 2
  rw [Real.sq_sqrt henergy]
  exact Summable.sum_le_tsum S
    (fun k _ => mul_nonneg (periodicH2Weight_pos k).le (sq_nonneg _))
    (summable_periodicSobolev_two hf hp)

/-- The bound holds in the continuous-map norm on the actual quotient torus. -/
theorem norm_continuousTorusLift_le_periodicH2
    {f : Space → ℂ} (hf : ContDiff ℝ 2 f) (hp : UnitPeriods f) :
    ‖continuousTorusLift f hf.continuous hp‖ ≤
      periodicSobolevNorm 2 f * periodicH2UniformConstant := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
  intro z
  exact norm_le_periodicH2UniformConstant_mul hf hp
    (toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val))

/-- Smooth periodic data admit uniform Fourier approximation without a
  separate coefficient-summability assumption. -/
theorem exists_periodicFourier_partialSum_uniform_of_h2
    {f : Space → ℂ} (hf : ContDiff ℝ 2 f) (hp : UnitPeriods f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset PeriodicFrequency, ∀ T : Finset PeriodicFrequency, S ⊆ T →
      ∀ x : Space, ‖(∑ k ∈ T, periodicCharacter k x * periodicFourierCoeff f k) - f x‖ < ε :=
  exists_periodicFourier_partialSum_uniform hf.continuous hp
    (summable_periodicFourierCoeff_of_h2_actual hf hp) hε

end NSFormalization.Paper1
