import NSFormalization.Section3.T11.H1Bridges
import NSFormalization.Section3.T11.EnstrophyInequality
import NSFormalization.Section3.T11.ClassicalRegularity
import NSFormalization.Section4.A04.EnstrophyBarrier

/-!
# Periodic H¹ restart adapters

The revised article `paper/revised/sections/02-preliminaries.tex:149–156` says
“For each initial velocity in the stated class and each force smooth into
every $H^m$ on compact time intervals” there is a maximal smooth velocity,
and “then it extends smoothly beyond $S$” under the squared H² criterion.
The separate uniform H¹ restart target is recorded in `research/P21/Targets.lean`.
This module retains the mean and uses the registered angular normalization κ=1.
-/
noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T12
open T20 (lTwoSqT gradientSqT laplacianSqT)
open scoped ContDiff ENNReal BigOperators

/-- The gradient carrier in B2 is precisely the finite physical L² norm. -/
theorem periodicGradient_bridgeT {z : SpatialField} (hz : ContDiff ℝ ∞ z) :
    periodicLpENorm 2 (gradientTensor z) =
      ENNReal.ofReal (Real.sqrt (gradientSqT z)) := by
  rw [gradientSqT, Real.sqrt_sq ENNReal.toReal_nonneg]
  exact (ENNReal.ofReal_toReal (memLp_gradientTensor hz).2.ne).symm

/-- Ordinary Parseval including the mean mode, in B2's carrier. -/
theorem hasSum_lTwoSqT {z : SpatialField} (hz : ContDiff ℝ ∞ z)
    (hp : IsPeriodicSpatial z) :
    HasSum (fun k : PeriodicFrequency =>
      ∑ i : Fin 3, ‖periodicFourierCoeff (fun x => (z x i : ℂ)) k‖ ^ 2)
      (lTwoSqT z) := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum 0 hz hp
  have h := hasSum_freqEnergyT (u := fun p => z p.2) (t := 0) hA
  have he : lTwoSqT z = ‖A‖ ^ 2 := by
    unfold lTwoSqT
    change (eLpNorm (torusLift z) 2 periodicTorusMeasure).toReal ^ 2 = _
    rw [← sobolevENorm_zero_eq hz hp, periodicSobolevENorm_eq hA, toReal_enorm]
  rw [he]
  simpa only [freqEnergyT, Real.rpow_zero, one_mul, velocityCoeffT] using h

/-- Full H¹ energy in B2's physical carriers. -/
theorem periodicHOne_bridgeT {z : SpatialField} (hz : ContDiff ℝ ∞ z)
    (hp : IsPeriodicSpatial z) :
    (periodicSobolevENorm 1 z).toReal ^ 2 = lTwoSqT z + gradientSqT z := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum 1 hz hp
  rw [periodicSobolevENorm_eq hA, toReal_enorm]
  have hG := T20.gradientSqT_meanFreeVelocity_eq_tsum
    (g := 0) (u := fun p => z p.2) (r := 0) hz hp
  simp only [gradientSqT, T20.gradientTensor_meanFreeVelocity] at hG
  have hs : Summable (fun k : PeriodicFrequency =>
      periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖periodicFourierCoeff (fun x => (z x i : ℂ)) k‖ ^ 2) := by
    convert (NSFormalization.Section3.T13.summable_homogeneous_total
      (s := (1 : ℝ)) (by norm_num) hp hz) using 1
    funext k
    rw [T20.homogeneousDatumWeight_one_sq]
  have h := (hasSum_lTwoSqT hz hp).add hs.hasSum
  change _ = lTwoSqT z + (periodicLpENorm 2 (gradientTensor z)).toReal ^ 2
  rw [hG]
  apply (hasSum_freqEnergyT (u := fun p => z p.2) (t := 0) hA).unique
  convert h using 1
  · funext k
    simp only [freqEnergyT, Real.rpow_one, velocityCoeffT]
    unfold periodicFrequencyWeight periodicAngularFrequencySq
    ring
  · simp only [T20.h1FreqEnergy, velocityCoeffT, periodicAngularFrequencySq]

/-- Full H² energy, with the exact ordered-Hessian/Laplacian normalization. -/
theorem periodicHTwo_bridgeT {z : SpatialField} (hz : ContDiff ℝ ∞ z)
    (hp : IsPeriodicSpatial z) :
    (periodicSobolevENorm 2 z).toReal ^ 2 =
      lTwoSqT z + 2 * gradientSqT z + laplacianSqT z := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum 2 hz hp
  rw [periodicSobolevENorm_eq hA, toReal_enorm]
  have hG := T20.gradientSqT_meanFreeVelocity_eq_tsum
    (g := 0) (u := fun p => z p.2) (r := 0) hz hp
  have hL := T20.laplacianSqT_meanFreeVelocity_eq_tsum
    (g := 0) (u := fun p => z p.2) (r := 0) hz hp
  simp only [gradientSqT, T20.gradientTensor_meanFreeVelocity] at hG
  simp only [laplacianSqT, T20.laplacian_meanFreeVelocity] at hL
  have hs (m : ℝ) (hm : 0 < m) :=
    NSFormalization.Section3.T13.summable_homogeneous_total (s := m) hm.le hp hz
  have hg : Summable (fun k : PeriodicFrequency =>
      periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖periodicFourierCoeff (fun x => (z x i : ℂ)) k‖ ^ 2) := by
    convert hs 1 (by norm_num) using 1
    funext k
    rw [T20.homogeneousDatumWeight_one_sq]
  have hl : Summable (fun k : PeriodicFrequency =>
      periodicAngularFrequencySq k ^ 2 *
        ∑ i : Fin 3, ‖periodicFourierCoeff (fun x => (z x i : ℂ)) k‖ ^ 2) := by
    convert hs 2 (by norm_num) using 1
    funext k
    rw [T20.homogeneousDatumWeight_two_eq]
  have h := ((hasSum_lTwoSqT hz hp).add (hg.hasSum.mul_left 2)).add hl.hasSum
  change _ = lTwoSqT z + 2 * (periodicLpENorm 2 (gradientTensor z)).toReal ^ 2 +
    (periodicLpENorm 2 (laplacian z)).toReal ^ 2
  rw [hG, hL]
  apply (hasSum_freqEnergyT (u := fun p => z p.2) (t := 0) hA).unique
  convert h using 1
  · funext k
    simp only [freqEnergyT, Real.rpow_two, velocityCoeffT]
    unfold periodicFrequencyWeight periodicAngularFrequencySq
    ring
  · simp only [T20.h1FreqEnergy, velocityCoeffT]

/-- B0's ordinary energy equals the B2 carrier. -/
theorem periodicL2Energy_eq_lTwoSqT {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    periodicL2Energy z = lTwoSqT z := by
  have h := periodicSobolevENorm_nat_toReal_sq_eq 0 hz hp
  simp only [Nat.cast_zero] at h
  change (periodicSobolevENorm 0 z).toReal ^ 2 = periodicL2Energy z at h
  rw [sobolevENorm_zero_eq hz hp] at h
  exact h.symm

/-- B0's component gradient energy equals the B2 carrier. -/
theorem periodicGradientEnergy_eq_gradientSqT {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    periodicGradientEnergy z = gradientSqT z := by
  have h := periodicSobolevENorm_one_toReal_sq_eq hz hp
  rw [periodicHOne_bridgeT hz hp, periodicL2Energy_eq_lTwoSqT hz hp] at h
  linarith

/-- Periodic Parseval identifies all ordered second partials with the Laplacian. -/
theorem periodicHessianEnergy_eq_laplacianSqT {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    periodicHessianEnergy z = laplacianSqT z := by
  have h := periodicSobolevENorm_two_toReal_sq_eq hz hp
  rw [periodicHTwo_bridgeT hz hp, periodicL2Energy_eq_lTwoSqT hz hp,
    periodicGradientEnergy_eq_gradientSqT hz hp] at h
  linarith

/-- B2 on compact interior intervals, with all three spatial bridges discharged. -/
theorem enstrophy_differential_on_IccT'
    {ν T r s : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : f ∈ forceClassT)
    (hν : 0 < ν) (hr : 0 < r) (hs : s < T) :
    ∀ t ∈ Icc r s,
      let Cν := (2 * convectionConstT) ^ 4 / (ν / 2) ^ 3 + (1 + ν) + (1 + 2 / ν)
      deriv (fun q => (periodicSobolevENorm 1 (fun x => w.velocity (q, x))).toReal ^ 2) t +
        ν * (periodicSobolevENorm 2 (fun x => w.velocity (t, x))).toReal ^ 2 ≤
      Cν * (1 + (periodicSobolevENorm 1 (fun x => w.velocity (t, x))).toReal ^ 2) ^ 3 +
        Cν * lTwoSqT (fun x => f (t, x)) := by
  apply enstrophy_differential_on_IccT w hf hν hr hs
  · intro q hq
    exact periodicHOne_bridgeT (classical_velocity_slice_contDiff w (Ioo_subset_Ico_self hq))
      (w.velocity_periodic q (Ioo_subset_Ico_self hq))
  · intro t ht
    have ht' : t ∈ Ico (0 : ℝ) T := ⟨(hr.trans_le ht.1).le, ht.2.trans_lt hs⟩
    exact (periodicHTwo_bridgeT (classical_velocity_slice_contDiff w ht')
      (w.velocity_periodic t ht')).le
  · intro t ht
    exact (periodicGradient_bridgeT (classical_velocity_slice_contDiff w
      ⟨(hr.trans_le ht.1).le, ht.2.trans_lt hs⟩)).le

/-- Squared registered energies are continuous up to the initial endpoint. -/
theorem continuousOn_periodicSobolevEnergyT {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (m : ℕ) :
    ContinuousOn (fun t => (periodicSobolevENorm (m : ℝ)
      (fun x => w.velocity (t, x))).toReal ^ 2) (Ico (0 : ℝ) T) :=
  (continuousOn_torusSobolevNormAt_velocity w m).pow 2

/-- Interior differentiability needs no force-class membership. -/
theorem differentiableAt_periodicSobolevEnergyT {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    DifferentiableAt ℝ (fun q => (periodicSobolevENorm (m : ℝ)
      (fun x => w.velocity (q, x))).toReal ^ 2) t :=
  (hasDerivAt_torusSobolevNormAt_sq w m ht).differentiableAt

/-- The force energy is bounded by the square of B0's norm cap. -/
theorem timeShiftT_lTwoSq_le_forceL2CapT {f : SpaceTimeField} (hf : MemForceT f)
    {S t₀ t : ℝ} (hS : 0 ≤ S) (ht₀ : t₀ ∈ Icc (0 : ℝ) S)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    lTwoSqT (fun x => timeShiftT t₀ f (t, x)) ≤ (forceL2CapT f S).toReal ^ 2 := by
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (forceL2CapT_ne_top hf hS)
      (timeShiftT_force_slice_le_forceL2CapT ht₀ ht)) 2

end NSFormalization.Section3.T11
