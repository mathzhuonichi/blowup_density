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

/-- Interpolation stage before the velocity Sobolev embedding. The velocity
L⁶ factor is still explicit; this is not yet the H¹/H² convection estimate. -/
theorem convection_interpolationT (z : SpatialField) (hz : SmoothPeriodicT z) :
    ENNReal.ofReal |∫ y : PeriodicTorus,
      torusLift (fun x ↦ (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)) y
        ∂periodicTorusMeasure| ≤
      periodicLpENorm 6 z *
        ((periodicLpENorm 2 (gradientTensor z)) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian z)) ^ (1 / 2 : ℝ)) *
        periodicLpENorm 2 (laplacian z) := by
  have hg := eLpNorm_three_interpolationT (torusLift (gradientTensor z))
    (T20.aestronglyMeasurable_torusLiftH1 (T20.continuous_gradientTensorH1 hz.1))
  have hg' : periodicLpENorm 3 (gradientTensor z) ≤
      (periodicLpENorm 2 (gradientTensor z)) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian z)) ^ (1 / 2 : ℝ) :=
    hg.trans (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow (gradient_six_le_laplacian_twoT z hz) (by norm_num)))
  rw [← Real.enorm_eq_ofReal_abs]
  exact ((enorm_integral_le_lintegral_enorm _).trans
    (lintegral_convection_holder_632T z hz)).trans
      (mul_le_mul' (mul_le_mul' le_rfl hg') le_rfl)

/-- Elementary localization route for the velocity embedding. The remaining
cutoff-gradient estimate must retain both the velocity L² and gradient L² terms. -/
theorem velocity_six_le_localized_gradientT (z : SpatialField) (hz : SmoothPeriodicT z) :
    periodicLpENorm 6 z ≤
      ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const *
        eLpNorm (gradientTensor (cutoffMul z)) 2 volume := by
  calc periodicLpENorm 6 z
      = eLpNorm z 6 (volume.restrict NSFormalization.Section3.T13.fundamentalCube) :=
        periodicLpENorm_eq_restrict z hz.2 6
    _ = eLpNorm (cutoffMul z) 6
        (volume.restrict NSFormalization.Section3.T13.fundamentalCube) :=
      (eLpNorm_congr_ae (ae_restrict_of_forall_mem
        NSFormalization.Section3.T13.measurableSet_fundamentalCube
        (fun x hx ↦ cutoffMul_eq_on_cube z hx))).symm
    _ ≤ eLpNorm (cutoffMul z) 6 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ _ := NSFormalization.Section4.A04.velocity_six_le_gradient_two
      (cutoffMul z) (smoothL2_cutoffMul hz.1)

open NSFormalization.Section4.A05 (dirDeriv gradTensor)

/-- Pointwise product estimate retaining the velocity term. -/
theorem norm_gradient_cutoffMul_leT {z : SpatialField} (hz : ContDiff ℝ ∞ z)
    (x : Space) :
    ‖gradientTensor (cutoffMul z) x‖ ≤
      3 * (cutoffGradBound * ‖z x‖ + ‖gradientTensor z x‖) := by
  have hB := cutoffGradBound_nonneg
  have hi (i : Fin 3) : ‖dirDeriv i (cutoffMul z) x‖ ≤
      cutoffGradBound * ‖z x‖ + ‖gradientTensor z x‖ := by
    rw [dirDeriv_cutoffMul_eq hz i]
    calc ‖cutoff x • dirDeriv i z x + dirDeriv i cutoff x • z x‖
        ≤ ‖cutoff x • dirDeriv i z x‖ + ‖dirDeriv i cutoff x • z x‖ := norm_add_le _ _
      _ ≤ ‖gradientTensor z x‖ + cutoffGradBound * ‖z x‖ := by
        rw [norm_smul, norm_smul]
        have hc : ‖cutoff x‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_range x).1]
          exact (cutoff_range x).2
        have hd := norm_dirDeriv_le_norm_gradTensor z i x
        have he := norm_dirDeriv_cutoff_le i x
        nlinarith [mul_le_mul hc hd (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1),
          mul_le_mul_of_nonneg_right he (norm_nonneg (z x))]
      _ = _ := by ring
  change ‖gradTensor (cutoffMul z) x‖ ≤ _
  rw [norm_gradTensor_eq]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have h0 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (hi 0)
    have h1 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (hi 1)
    have h2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (hi 2)
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (cutoffGradBound * ‖z x‖ + ‖gradientTensor z x‖)]

open Metric NSFormalization.Section3.T13
open scoped Topology

/-- Periodic majorant for the first derivative of the localized velocity. -/
def gradientMajorantT (z : SpatialField) (x : Space) : ℝ :=
  3 * (cutoffGradBound * ‖z x‖ + ‖gradientTensor z x‖)

theorem gradientMajorantT_nonneg (z : SpatialField) (x : Space) :
    0 ≤ gradientMajorantT z x := by
  have := cutoffGradBound_nonneg
  unfold gradientMajorantT
  positivity

theorem continuous_gradientMajorantT {z : SpatialField} (hz : ContDiff ℝ ∞ z) :
    Continuous (gradientMajorantT z) :=
  continuous_const.mul ((continuous_const.mul hz.continuous.norm).add
    (continuous_norm_gradTensor hz))

theorem isPeriodicSpatial_gradientMajorantT {z : SpatialField} (hz : IsPeriodicSpatial z) :
    IsPeriodicSpatial (gradientMajorantT z) := by
  intro x j
  unfold gradientMajorantT
  rw [hz x j, show gradientTensor z (x + coordinateVector j) = gradientTensor z x from
    isPeriodicSpatial_gradientTensor hz x j]

theorem gradient_cutoffMul_eq_zeroT (z : SpatialField) {x : Space}
    (hx : x ∉ closedBall (0 : Space) 3) : gradientTensor (cutoffMul z) x = 0 := by
  have hw : EqOn (cutoffMul z) 0 ((closedBall (0 : Space) 3)ᶜ) := by
    intro y hy
    by_contra h
    exact hy (support_cutoffMul_subset z h)
  apply PiLp.ext
  intro i
  exact eqOn_zero_dirDeriv isClosed_closedBall.isOpen_compl hw i hx

theorem enorm_gradient_cutoffMul_leT {v : SpatialField} (hv : ContDiff ℝ ∞ v) (z : Space) :
    ‖gradientTensor (cutoffMul v) z‖ₑ ^ (2 : ℝ)
      ≤ (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) z
          * ‖gradientMajorantT v z‖ₑ ^ (2 : ℝ) := by
  by_cases hz : z ∈ closedBall (0 : Space) 3
  · rw [Set.indicator_of_mem hz, one_mul]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (gradientMajorantT_nonneg v z)]
    exact norm_gradient_cutoffMul_leT hv z
  · rw [Set.indicator_of_notMem hz, gradient_cutoffMul_eq_zeroT v hz, zero_mul, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

/-! ## The lattice tiling estimate -/



theorem lintegral_gradient_cutoffMul_leT {v : SpatialField} (hv : SmoothPeriodicT v) :
    ∫⁻ x : Space, ‖gradientTensor (cutoffMul v) x‖ₑ ^ (2 : ℝ)
      ≤ 343 * ∫⁻ y in halfOpenCube, ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ) := by
  have hmajM : Measurable (fun y : Space => ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ)) :=
    measurable_enn_sq.comp (continuous_gradientMajorantT hv.1).measurable.enorm
  have hmeasLHS : Measurable (fun x : Space => ‖gradientTensor (cutoffMul v) x‖ₑ ^ (2 : ℝ)) :=
    measurable_enn_sq.comp
      (T20.continuous_gradientTensorH1 (contDiff_cutoffMul hv.1)).measurable.enorm
  have hind : Measurable ((closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator measurableSet_closedBall
  have hterm : ∀ n : PeriodicFrequency, Measurable (fun y : Space =>
      (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (y + latticeVector n)
        * ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ)) := fun n =>
    (hind.comp (measurable_id.add_const (latticeVector n))).mul hmajM
  rw [lintegral_eq_tsum_halfOpenCube hmeasLHS]
  calc ∑' n : PeriodicFrequency, ∫⁻ y in halfOpenCube,
          ‖gradientTensor (cutoffMul v) (y + latticeVector n)‖ₑ ^ (2 : ℝ)
      ≤ ∑' n : PeriodicFrequency, ∫⁻ y in halfOpenCube,
          (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (y + latticeVector n)
            * ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ) := by
        refine ENNReal.tsum_le_tsum fun n => lintegral_mono fun y => ?_
        have h := enorm_gradient_cutoffMul_leT hv.1 (y + latticeVector n)
        rwa [periodic_latticeVector (isPeriodicSpatial_gradientMajorantT hv.2) y n] at h
    _ = ∫⁻ y in halfOpenCube, ∑' n : PeriodicFrequency,
          (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (y + latticeVector n)
            * ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ) :=
        (lintegral_tsum fun n => (hterm n).aemeasurable).symm
    _ = ∫⁻ y in halfOpenCube, (∑' n : PeriodicFrequency,
          (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (y + latticeVector n))
            * ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ) := by
        refine lintegral_congr fun y => ?_
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ y in halfOpenCube, (343 : ℝ≥0∞) * ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ) :=
        lintegral_mono fun y => mul_le_mul' (lattice_count_le y) le_rfl
    _ = 343 * ∫⁻ y in halfOpenCube, ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ) :=
        lintegral_const_mul _ hmajM

theorem eLpNorm_gradient_cutoffMul_leT {v : SpatialField} (hv : SmoothPeriodicT v) :
    eLpNorm (gradientTensor (cutoffMul v)) 2 volume
      ≤ 343 * eLpNorm (gradientMajorantT v) 2 (volume.restrict fundamentalCube) := by
  have hQ : (volume : Measure Space).restrict fundamentalCube
      = (volume : Measure Space).restrict halfOpenCube :=
    Measure.restrict_congr_set fundamentalCube_ae_eq_halfOpenCube
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), hQ,
    show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  calc (∫⁻ x : Space, ‖gradientTensor (cutoffMul v) x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ (343 * ∫⁻ y in halfOpenCube, ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_gradient_cutoffMul_leT hv) (by norm_num)
    _ = (343 : ℝ≥0∞) ^ (1 / (2 : ℝ))
        * (∫⁻ y in halfOpenCube, ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ 343 * (∫⁻ y in halfOpenCube, ‖gradientMajorantT v y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        gcongr
        calc (343 : ℝ≥0∞) ^ (1 / (2 : ℝ)) ≤ (343 : ℝ≥0∞) ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 343 := ENNReal.rpow_one _


/-- The localized gradient has the two required periodic L² terms. -/
theorem cutoff_gradient_two_leT (z : SpatialField) (hz : SmoothPeriodicT z) :
    eLpNorm (gradientTensor (cutoffMul z)) 2 volume ≤
      343 * (3 * (ENNReal.ofReal cutoffGradBound * periodicLpENorm 2 z +
        periodicLpENorm 2 (gradientTensor z))) := by
  let μ := volume.restrict fundamentalCube
  have hm1 : AEStronglyMeasurable (fun x => cutoffGradBound * ‖z x‖) μ :=
    (continuous_const.mul hz.1.continuous.norm).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x => ‖gradientTensor z x‖) μ :=
    (continuous_norm_gradTensor hz.1).aestronglyMeasurable
  have hnorm : ‖cutoffGradBound‖ₑ = ENNReal.ofReal cutoffGradBound := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg cutoffGradBound_nonneg]
  have heq : gradientMajorantT z = (3 : ℝ) •
      (fun x => cutoffGradBound * ‖z x‖ + ‖gradientTensor z x‖) := rfl
  have hbound : eLpNorm (gradientMajorantT z) 2 μ ≤
      3 * (ENNReal.ofReal cutoffGradBound * eLpNorm z 2 μ +
        eLpNorm (gradientTensor z) 2 μ) := by
    calc eLpNorm (gradientMajorantT z) 2 μ
        ≤ ‖(3 : ℝ)‖ₑ * eLpNorm
          (fun x => cutoffGradBound * ‖z x‖ + ‖gradientTensor z x‖) 2 μ := by
            rw [heq]
            exact eLpNorm_const_smul_le
      _ ≤ ‖(3 : ℝ)‖ₑ * (eLpNorm (fun x => cutoffGradBound * ‖z x‖) 2 μ +
          eLpNorm (fun x => ‖gradientTensor z x‖) 2 μ) := by
        gcongr
        exact eLpNorm_add_le hm1 hm2 (by norm_num)
      _ ≤ ‖(3 : ℝ)‖ₑ * (‖cutoffGradBound‖ₑ * eLpNorm (fun x => ‖z x‖) 2 μ +
          eLpNorm (fun x => ‖gradientTensor z x‖) 2 μ) := by
        gcongr
        change eLpNorm (cutoffGradBound • (fun x => ‖z x‖)) 2 μ ≤ _
        exact eLpNorm_const_smul_le
      _ = _ := by rw [hnorm, eLpNorm_norm, eLpNorm_norm, ← ofReal_norm]; norm_num
  have h := (eLpNorm_gradient_cutoffMul_leT hz).trans (mul_le_mul' le_rfl hbound)
  simpa only [μ, ← periodicLpENorm_eq_restrict z hz.2 2,
    ← periodicLpENorm_eq_restrict (gradientTensor z) (isPeriodicSpatial_gradientTensor hz.2) 2]
    using h

/-- Explicit mean-retaining velocity embedding constant. -/
def velocitySixConstT : ℝ :=
  3 * 343 * NSFormalization.Section4.A05.gradientL6Const * (1 + cutoffGradBound)

/-- Inhomogeneous Sobolev embedding on the normalized torus; no mean condition. -/
theorem velocity_six_le_gradient_twoT (z : SpatialField) (hz : SmoothPeriodicT z) :
    periodicLpENorm 6 z ≤ ENNReal.ofReal velocitySixConstT *
      (periodicLpENorm 2 z + periodicLpENorm 2 (gradientTensor z)) := by
  have hA := NSFormalization.Section4.A05.gradientL6Const_pos.le
  have hB := cutoffGradBound_nonneg
  have h := (velocity_six_le_localized_gradientT z hz).trans
    (mul_le_mul' le_rfl (cutoff_gradient_two_leT z hz))
  have hC : ENNReal.ofReal velocitySixConstT =
      3 * 343 * ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const *
        (1 + ENNReal.ofReal cutoffGradBound) := by
    unfold velocitySixConstT
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by norm_num) hB]
    norm_num
  apply h.trans
  rw [hC]
  have hb : ENNReal.ofReal cutoffGradBound * periodicLpENorm 2 z +
      periodicLpENorm 2 (gradientTensor z) ≤
      (1 + ENNReal.ofReal cutoffGradBound) *
        (periodicLpENorm 2 z + periodicLpENorm 2 (gradientTensor z)) := by
    rw [mul_add]
    exact add_le_add (mul_le_mul' (le_add_left le_rfl) le_rfl)
      (by simpa using mul_le_mul' (show (1 : ℝ≥0∞) ≤ 1 + ENNReal.ofReal cutoffGradBound from
        le_add_right le_rfl) (le_refl (periodicLpENorm 2 (gradientTensor z))))
  calc _ = (3 * 343 * ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const) *
      (ENNReal.ofReal cutoffGradBound * periodicLpENorm 2 z +
        periodicLpENorm 2 (gradientTensor z)) := by ring
    _ ≤ _ := by
      rw [mul_assoc (3 * 343 * ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const)]
      exact mul_le_mul' le_rfl hb

end NSFormalization.Section3.T11
