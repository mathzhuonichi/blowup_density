import NSFormalization.Section3.T11.EnergyIdentity
import NSFormalization.Section3.T20.H1Energy
import NSFormalization.Section4.A04.EnstrophyInequality

/-!
# P21 Route B, B2: periodic inhomogeneous enstrophy

The revised article, `paper/revised/sections/02-preliminaries.tex:149–156`,
states: “For each initial velocity in the stated class and each force smooth into
every $H^m$ on compact time intervals” there is a unique maximal smooth velocity,
and “then it extends smoothly beyond $S$” under the squared H² integral criterion.
Lines 165–168 explicitly retain nonzero periodic mean through mean reduction.
This module concerns the separate H¹-uniform restart obligation.

The periodic Fourier weight is 1+|2πk|²: the physical gradient weight is one,
unlike the whole-space convention of B1. No smallness estimate is used.
-/

noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal

/-- Differentiated full H¹ energy, retaining the zero Fourier mode.
The pairings here are H¹ pairings, before spatial integration by parts. -/
theorem inhomogeneousEnergyIdentityT
    {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : f ∈ forceClassT)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G F N : PeriodicSobolev 1}
    (hG : IsPeriodicDatum 1 (fun x ↦ w.velocity (t, x)) G)
    (hF : IsPeriodicDatum 1 (fun x ↦ f (t, x)) F)
    (hN : IsPeriodicDatum 1 (fun x ↦ convectionFieldT w.velocity (t, x)) N) :
    HasDerivAt
      (fun s ↦ (periodicSobolevENorm 1 (fun x ↦ w.velocity (s, x))).toReal ^ 2)
      (-2 * ν * torusGradientNormAt 1 w.velocity t ^ 2 +
        2 * torusRealPairing G F - 2 * torusRealPairing G N) t := by
  convert
    (energyIdentity_of_classical w hf.1 1 ht (Gm := G) (Fm := F) (Nm := N)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hG)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hF)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hN)) using 1 <;>
    norm_num [torusSobolevNormAt, torusRealPairing]

/-- Haar Hölder with velocity in L⁶, gradient in L³, Laplacian in L². -/
theorem lintegral_convection_holder_632T (z : SpatialField) (hz : SmoothPeriodicT z) :
    ∫⁻ y, ‖torusLift
      (fun x ↦ (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)) y‖ₑ
        ∂periodicTorusMeasure ≤
      periodicLpENorm 6 z * periodicLpENorm 3 (gradientTensor z) *
        periodicLpENorm 2 (laplacian z) := by
  have h := T20.lintegral_enorm_mul_three_le_torus_three_six_two
    (T20.aestronglyMeasurable_torusLiftH1 (T20.continuous_gradientTensorH1 hz.1))
    (T20.aestronglyMeasurable_torusLiftH1 hz.1.continuous)
    (T20.aestronglyMeasurable_torusLiftH1 (contDiff_laplacian hz.1).continuous)
  have hp : ∀ y : PeriodicTorus,
      ‖torusLift (fun x ↦ (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)) y‖ₑ ≤
        ‖torusLift (gradientTensor z) y‖ₑ * ‖torusLift z y‖ₑ *
          ‖torusLift (laplacian z) y‖ₑ := by
    intro y
    simpa only [torusLift, NSFormalization.Paper1.torusLift, mul_comm] using T20.enorm_inner_advection_leH1 z (laplacian z)
      (NavierStokes.PeriodicIntegration.toSpace
        ((UnitAddTorus.measurableEquivPiIoc (0 : NavierStokes.PeriodicIntegration.Coords) y).val))
  exact (lintegral_mono hp).trans (by simpa only [periodicLpENorm, mul_comm] using h)

/-- L³ interpolation between L² and L⁶, including infinite norms. -/
theorem eLpNorm_three_interpolationT {E : Type*} [NormedAddCommGroup E] (g : PeriodicTorus → E)
    (hg : AEStronglyMeasurable g periodicTorusMeasure) :
    eLpNorm g 3 periodicTorusMeasure ≤ (eLpNorm g 2 periodicTorusMeasure) ^ (1 / 2 : ℝ) *
      (eLpNorm g 6 periodicTorusMeasure) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (hg.enorm.pow_const (2 : ℝ)) (hg.enorm.pow_const (6 : ℝ))
    (p := (3 / 4 : ℝ)) (q := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have he : (fun x => (‖g x‖ₑ ^ (2 : ℝ)) ^ (3 / 4 : ℝ) *
      (‖g x‖ₑ ^ (6 : ℝ)) ^ (1 / 4 : ℝ)) = fun x => ‖g x‖ₑ ^ (3 : ℝ) := by
    funext x
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  rw [he] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
    ← ENNReal.rpow_mul] at hh
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3 : ℝ≥0∞) ≠ 0)
    (by norm_num : (3 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (6 : ℝ≥0∞) ≠ 0)
    (by norm_num : (6 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  convert hh using 1 <;> norm_num


theorem young_quarticT {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    a * b ^ 3 ≤ ε * b ^ 4 + a ^ 4 / ε ^ 3 := by
  by_cases h : b ≤ a / ε
  · have hh : a * b ^ 3 ≤ a * (a / ε) ^ 3 := by gcongr
    have he : a * (a / ε) ^ 3 = a ^ 4 / ε ^ 3 := by ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_left (by positivity))
  · have hh : a ≤ ε * b := by
      have := (div_lt_iff₀ hε).mp (lt_of_not_ge h)
      linarith
    have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg hb 3)
    have he : ε * b * b ^ 3 = ε * b ^ 4 := by ring
    rw [he] at hm
    exact hm.trans (le_add_of_nonneg_right (by positivity))


theorem young_three_quartersT {C Y Z ε : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hZ : 0 ≤ Z) (hε : 0 < ε) :
    C * Y ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ) ≤
      ε * Z + C ^ 4 / ε ^ 3 * Y ^ 3 := by
  have h := young_quarticT (a := C * Y ^ (3 / 4 : ℝ))
    (b := Z ^ (1 / 4 : ℝ)) (by positivity) (by positivity) hε
  have h3 : (Z ^ (1 / 4 : ℝ)) ^ (3 : ℕ) = Z ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ]; norm_num
  have h4 : (Z ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = Z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ]; norm_num
  have hY4 : (Y ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = Y ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY]; norm_num
  rw [h3, h4, mul_pow, hY4] at h
  convert h using 1 <;> ring


theorem young_two_factorsT {a b ε : ℝ} (hε : 0 < ε) :
    2 * a * b ≤ ε * b ^ 2 + a ^ 2 / ε := by
  have h : 2 * a * b ≤ (ε ^ 2 * b ^ 2 + a ^ 2) / ε :=
    (le_div_iff₀ hε).2 (by nlinarith [sq_nonneg (ε * b - a)])
  convert h using 1 <;> field_simp


/-- Cubic absorption with the inhomogeneous energy in the nonlinear bound.
In particular the constant mode in U is retained. This is scalar algebra,
not a classical-solution differential inequality. -/
theorem weighted_cubic_assemblyT {ν C U G L F N P Q d Y Z : ℝ}
    (hν : 0 < ν) (hC : 0 ≤ C)
    (hU : 0 ≤ U) (hG : 0 ≤ G) (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hY : Y = U + G) (hZ : Z ≤ U + 2 * G + L)
    (hd : d = -2 * ν * G - 2 * ν * L + 2 * N + 2 * P - 2 * Q)
    (hN : |N| ≤ C * Y ^ (3 / 4 : ℝ) * L ^ (3 / 4 : ℝ))
    (hP : P ≤ Real.sqrt U * Real.sqrt F)
    (hQ : -Q ≤ Real.sqrt F * Real.sqrt L) :
    d + ν * Z ≤
      ((2 * C) ^ 4 / (ν / 2) ^ 3 + (1 + ν)) * (1 + Y) ^ 3 +
        (1 + 2 / ν) * F := by
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hn := young_three_quartersT (C := 2 * C) (Y := Y) (Z := L)
    (by positivity) hY0 hL (show 0 < ν / 2 by positivity)
  have hn' : 2 * N ≤ ν / 2 * L + (2 * C) ^ 4 / (ν / 2) ^ 3 * Y ^ 3 := by
    have h := mul_le_mul_of_nonneg_left ((le_abs_self N).trans hN) (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [h, hn]
  have hp : 2 * P ≤ U + F := by
    have h := young_two_factorsT (a := Real.sqrt U) (b := Real.sqrt F) (ε := 1) (by norm_num)
    rw [Real.sq_sqrt hU, Real.sq_sqrt hF] at h
    nlinarith
  have hq : -2 * Q ≤ ν / 2 * L + (2 / ν) * F := by
    have h := young_two_factorsT (a := Real.sqrt F) (b := Real.sqrt L)
      (ε := ν / 2) (by positivity)
    rw [Real.sq_sqrt hL, Real.sq_sqrt hF] at h
    have he : F / (ν / 2) = (2 / ν) * F := by ring
    rw [he] at h
    nlinarith
  have hm : Y ^ 3 ≤ (1 + Y) ^ 3 := by gcongr; linarith
  have hm1 : Y ≤ (1 + Y) ^ 3 := by nlinarith [sq_nonneg Y, pow_nonneg hY0 3]
  have hc : 0 ≤ (2 * C) ^ 4 / (ν / 2) ^ 3 := by positivity
  have hb := mul_le_mul_of_nonneg_left hm hc
  have hb1 := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 1 + ν by positivity)
  have hz := mul_le_mul_of_nonneg_left hZ hν.le
  have hUY : U ≤ Y := by linarith
  have hu := mul_le_mul_of_nonneg_left hUY (show 0 ≤ 1 + ν by positivity)
  nlinarith only [hn', hp, hq, hb, hb1, hz, hu, hd]

/-- The gradient L⁶ estimate applies without a zero-mean assumption on z:
subtracting its mean leaves both derivatives unchanged. -/
theorem gradient_six_le_laplacian_twoT (z : SpatialField) (hz : SmoothPeriodicT z) :
    periodicLpENorm 6 (gradientTensor z) ≤
      ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian z) := by
  have hs : SmoothPeriodicT (meanZeroPartT z) :=
    ⟨hz.1.sub contDiff_const, fun x j ↦ by simp only [meanZeroPartT, hz.2 x j]⟩
  have hm := (mean_decomposition z hz.2
    ((memLp_torusLift_vector hz.1.continuous 1).integrable le_rfl)).2
  have h := gradientLSix (meanZeroPartT z) hs hm
  rw [show gradientTensor (meanZeroPartT z) = gradientTensor z from
    T20.gradientTensor_sub_const z (meanT z),
    show laplacian (meanZeroPartT z) = laplacian z from
    T20.laplacian_sub_const z (meanT z)] at h
  exact h

end NSFormalization.Section3.T11



