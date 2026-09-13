import NSFormalization.Paper1.PeriodicFiniteL3
import NSFormalization.Paper1.PeriodicSobolevHilbert

/-!
# Finite-spectral critical interface for Paper 1

The manuscript's critical torus estimate is an infinite-frequency,
mean-zero `H^(1/2) → L^3` statement and remains open.  This file records the
strict finite-frequency consequence that is available unconditionally: the
finite Fourier sum has an explicit `sqrt (card S)` loss.  The half-order
energy is then bounded by the actual inhomogeneous periodic Sobolev energy.
The cardinality factor is retained deliberately; no uniform critical
embedding is asserted.
-/

noncomputable section
namespace NSFormalization.Paper1

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal

/-- A finite half-order energy is bounded by the complete periodic
`H^(1/2)` spectral square.  The finite-support and summability hypotheses are
explicit, so this is not a default-zero `tsum` argument. -/
theorem homogeneousHalfEnergy_le_periodicSobolevSq
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) :
    homogeneousHalfEnergy (fun k => periodicFourierCoeff f k) S ≤
      periodicSobolevSq (1 / 2 : ℝ) f := by
  have hfinite : homogeneousHalfEnergy (fun k => periodicFourierCoeff f k) S ≤
      ∑ k ∈ S, periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
        ‖periodicFourierCoeff f k‖ ^ 2 := by
    exact homogeneousHalfEnergy_le_bessel
      (fun k => periodicFourierCoeff f k) S
  have hsum : Summable (fun k : PeriodicFrequency =>
      periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
        ‖periodicFourierCoeff f k‖ ^ 2) :=
    summable_periodicSobolev hf hp (by norm_num)
  have hle : (∑ k ∈ S, periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
      ‖periodicFourierCoeff f k‖ ^ 2) ≤
      ∑' k : PeriodicFrequency,
        periodicFrequencyWeight k ^ (1 / 2 : ℝ) *
          ‖periodicFourierCoeff f k‖ ^ 2 := by
    exact Summable.sum_le_tsum S
      (fun k _ => mul_nonneg
        (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) _)
        (sq_nonneg _)) hsum
  exact hfinite.trans (by simpa [periodicSobolevSq] using hle)

/-- The finite mean-zero cubic estimate with the explicit cardinality loss,
now expressed using the actual periodic `H^(1/2)` Sobolev norm. -/
theorem cubeIntegral_norm_fin_periodicFourier_sum_pow_three_le_of_periodicSobolev
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    (S : Finset PeriodicFrequency) (hmean : cubeIntegral f = 0) :
    cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k) S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt S.card * periodicSobolevNorm (1 / 2 : ℝ) f) ^ (3 : ℕ) := by
  have hbase := cubeIntegral_norm_fin_periodicFourier_sum_pow_three_le_of_meanZero
    f S hmean
  have henergy : homogeneousHalfEnergy (fun k => periodicFourierCoeff f k) S ≤
      periodicSobolevSq (1 / 2 : ℝ) f :=
    homogeneousHalfEnergy_le_periodicSobolevSq hf hp S
  have hsqrt : Real.sqrt (homogeneousHalfEnergy
      (fun k => periodicFourierCoeff f k) S) ≤
      Real.sqrt (periodicSobolevSq (1 / 2 : ℝ) f) :=
    Real.sqrt_le_sqrt henergy
  have hmul : Real.sqrt S.card * Real.sqrt (homogeneousHalfEnergy
      (fun k => periodicFourierCoeff f k) S) ≤
      Real.sqrt S.card * Real.sqrt (periodicSobolevSq (1 / 2 : ℝ) f) := by
    exact mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  have hpow := pow_le_pow_left₀ (by positivity :
      0 ≤ Real.sqrt S.card * Real.sqrt (homogeneousHalfEnergy
        (fun k => periodicFourierCoeff f k) S) ) hmul 3
  change cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k) S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt S.card * Real.sqrt (periodicSobolevSq (1 / 2 : ℝ) f)) ^ (3 : ℕ)
  exact hbase.trans hpow

end NSFormalization.Paper1
