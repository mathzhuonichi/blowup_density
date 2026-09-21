import NSFormalization.Paper1.PeriodicFourierDerivative
import NSFormalization.Paper1.PeriodicMeanZeroEstimate

/-! Finite Fourier L3 control on the unit periodic cube.

This is a genuinely finite-spectral estimate.  It records the elementary
bound by the coefficient l1 sum and deliberately does not claim the critical
H^(1/2) -> L3 embedding (which would require a uniform infinite-frequency
argument).
-/
noncomputable section
namespace NSFormalization.Paper1
open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff

/-- Physical finite Fourier partial sum. -/
def finitePeriodicFourierSum (c : PeriodicFrequency → ℂ)
    (S : Finset PeriodicFrequency) : Space → ℂ :=
  fun x => ∑ k ∈ S, periodicCharacter k x * c k

@[simp] theorem finitePeriodicFourierSum_apply (c : PeriodicFrequency → ℂ)
    (S : Finset PeriodicFrequency) (x : Space) :
    finitePeriodicFourierSum c S x = ∑ k ∈ S, periodicCharacter k x * c k := rfl

theorem continuous_finitePeriodicFourierSum (c : PeriodicFrequency → ℂ)
    (S : Finset PeriodicFrequency) :
    Continuous (finitePeriodicFourierSum c S) := by
  unfold finitePeriodicFourierSum
  apply continuous_finset_sum
  intro k hk
  exact (periodicCharacter_smooth k).continuous.mul continuous_const

private theorem norm_periodicCharacter (k : PeriodicFrequency) (x : Space) :
    ‖periodicCharacter k x‖ = 1 := by
  rw [periodicCharacter_eq_mFourier]
  change ‖∏ i : Fin 3, fourier (k i) (x i : UnitAddCircle)‖ = 1
  simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem norm_finitePeriodicFourierSum_le (c : PeriodicFrequency → ℂ)
    (S : Finset PeriodicFrequency) (x : Space) :
    ‖finitePeriodicFourierSum c S x‖ ≤ ∑ k ∈ S, ‖c k‖ := by
  unfold finitePeriodicFourierSum
  calc
    ‖∑ k ∈ S, periodicCharacter k x * c k‖ ≤
        ∑ k ∈ S, ‖periodicCharacter k x * c k‖ := norm_sum_le S _
    _ = ∑ k ∈ S, ‖c k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [norm_periodicCharacter]

/-- The finite Fourier partial sum has cube-integrated cubic norm bounded by
its coefficient l1 sum cubed. -/
theorem cubeIntegral_norm_fin_fourier_sum_pow_three_le
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency) :
    cubeIntegral (fun x => ‖finitePeriodicFourierSum c S x‖ ^ (3 : ℕ)) ≤
      (∑ k ∈ S, ‖c k‖) ^ (3 : ℕ) := by
  let B : ℝ := ∑ k ∈ S, ‖c k‖
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpoint : ∀ x : Space,
      ‖finitePeriodicFourierSum c S x‖ ^ (3 : ℕ) ≤ B ^ (3 : ℕ) := by
    intro x
    have hx : ‖finitePeriodicFourierSum c S x‖ ≤ B := by
      exact norm_finitePeriodicFourierSum_le c S x
    exact pow_le_pow_left₀ (norm_nonneg _) hx 3
  have hleft : Integrable (fun y : Coords =>
      ‖finitePeriodicFourierSum c S (toSpace y)‖ ^ (3 : ℕ)) cubeMeasure := by
    have hc : Continuous (fun x : Space =>
        ‖finitePeriodicFourierSum c S x‖ ^ (3 : ℕ)) :=
      (continuous_finitePeriodicFourierSum c S).norm.pow 3
    exact integrable_cube hc
  have hright : Integrable (fun y : Coords => B ^ (3 : ℕ)) cubeMeasure := by
    have hc : Continuous (fun _ : Space => B ^ (3 : ℕ)) := continuous_const
    exact integrable_cube hc
  have hmono : (∫ y : Coords, ‖finitePeriodicFourierSum c S (toSpace y)‖ ^ (3 : ℕ) ∂cubeMeasure) ≤
      ∫ y : Coords, B ^ (3 : ℕ) ∂cubeMeasure := by
    apply integral_mono_ae hleft hright
    filter_upwards [] with y
    exact hpoint (toSpace y)
  have hcube : cubeMeasure Set.univ = 1 := by
    rw [cubeMeasure, Measure.restrict_apply_univ, cube, Real.volume_Icc_pi]
    simp
  change (∫ y : Coords, ‖finitePeriodicFourierSum c S (toSpace y)‖ ^ (3 : ℕ) ∂cubeMeasure) ≤
      B ^ (3 : ℕ)
  simpa [MeasureTheory.integral_const, Measure.real, hcube, smul_eq_mul] using hmono

/-- Mean-zero finite Fourier cubic estimate with the explicit finite-support
constant.  The cardinality factor is retained; removing it is the genuine
critical Sobolev step and is not asserted here. -/
theorem cubeIntegral_norm_fin_fourier_sum_pow_three_le_of_meanZero
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency)
    (hzero : c 0 = 0) :
    cubeIntegral (fun x => ‖finitePeriodicFourierSum c S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt S.card * Real.sqrt (homogeneousHalfEnergy c S)) ^ (3 : ℕ) := by
  let A : ℝ := ∑ k ∈ S, ‖c k‖
  let E : ℝ := Real.sqrt (homogeneousHalfEnergy c S)
  let C : ℝ := Real.sqrt S.card
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcs : A ≤ E * C := by
    dsimp [A, E, C]
    calc
      (∑ k ∈ S, ‖c k‖) ≤
          Real.sqrt (∑ k ∈ S, (‖c k‖)^2) *
            Real.sqrt (∑ k ∈ S, (1 : ℝ)^2) := by
        simpa only [mul_one] using Real.sum_mul_le_sqrt_mul_sqrt S
          (fun k => ‖c k‖) (fun _ => (1 : ℝ))
      _ = Real.sqrt (∑ k ∈ S, ‖c k‖ ^ 2) * Real.sqrt S.card := by
        congr 1
        simp
      _ ≤ Real.sqrt (homogeneousHalfEnergy c S) * Real.sqrt S.card := by
        exact mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (finite_meanZero_l2_le_homogeneousHalfEnergy_one c S hzero))
          (Real.sqrt_nonneg _)
  have hpoint : ∀ x : Space,
      ‖finitePeriodicFourierSum c S x‖ ^ (3 : ℕ) ≤
        (Real.sqrt S.card * Real.sqrt (homogeneousHalfEnergy c S)) ^ (3 : ℕ) := by
    intro x
    have hx : ‖finitePeriodicFourierSum c S x‖ ≤ A :=
      (norm_finitePeriodicFourierSum_le c S x).trans_eq rfl
    have hxa : ‖finitePeriodicFourierSum c S x‖ ≤ E * C := hx.trans hcs
    have hEC : E * C = C * E := by ring
    rw [hEC] at hxa
    exact pow_le_pow_left₀ (norm_nonneg _) hxa 3
  have hleft : Integrable (fun y : Coords =>
      ‖finitePeriodicFourierSum c S (toSpace y)‖ ^ (3 : ℕ)) cubeMeasure := by
    exact integrable_cube ((continuous_finitePeriodicFourierSum c S).norm.pow 3)
  have hright : Integrable (fun y : Coords =>
      (Real.sqrt S.card * Real.sqrt (homogeneousHalfEnergy c S)) ^ (3 : ℕ)) cubeMeasure := by
    exact integrable_cube continuous_const
  have hmono : (∫ y : Coords, ‖finitePeriodicFourierSum c S (toSpace y)‖ ^ (3 : ℕ) ∂cubeMeasure) ≤
      ∫ y : Coords, (Real.sqrt S.card * Real.sqrt (homogeneousHalfEnergy c S)) ^ (3 : ℕ) ∂cubeMeasure := by
    apply integral_mono_ae hleft hright
    filter_upwards [] with y
    exact hpoint (toSpace y)
  have hcube : cubeMeasure Set.univ = 1 := by
    rw [cubeMeasure, Measure.restrict_apply_univ, cube, Real.volume_Icc_pi]
    simp
  change (∫ y : Coords, ‖finitePeriodicFourierSum c S (toSpace y)‖ ^ (3 : ℕ) ∂cubeMeasure) ≤
      (Real.sqrt S.card * Real.sqrt (homogeneousHalfEnergy c S)) ^ (3 : ℕ)
  simpa [MeasureTheory.integral_const, Measure.real, hcube, smul_eq_mul] using hmono

/-- Fourier-coefficient specialization with a vanishing physical cube mean. -/
theorem cubeIntegral_norm_fin_periodicFourier_sum_pow_three_le_of_meanZero
    (f : Space → ℂ) (S : Finset PeriodicFrequency) (hmean : cubeIntegral f = 0) :
    cubeIntegral (fun x =>
      ‖finitePeriodicFourierSum (fun k => periodicFourierCoeff f k) S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt S.card *
        Real.sqrt (homogeneousHalfEnergy (fun k => periodicFourierCoeff f k) S)) ^ (3 : ℕ) := by
  apply cubeIntegral_norm_fin_fourier_sum_pow_three_le_of_meanZero
  exact (periodicFourierCoeff_zero_eq_zero_iff f).mpr hmean

end NSFormalization.Paper1
