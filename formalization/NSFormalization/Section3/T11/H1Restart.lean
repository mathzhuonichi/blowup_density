import NSFormalization.Section3.T11.H1Bridges
import NSFormalization.Section3.T11.EnstrophyInequality
import NSFormalization.Section3.T11.ExistenceInputH3
import NSFormalization.Section3.T11.PairingBound
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
open T20 (periodicPairing lTwoSqT gradientSqT laplacianSqT)
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

/-- The differentiated energy only needs smooth forcing. -/
theorem inhomogeneousEnergyIdentity_smoothT
    {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f)
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
    (energyIdentity_of_classical w hf 1 ht (Gm := G) (Fm := F) (Nm := N)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hG)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hF)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hN)) using 1 <;>
    norm_num [torusSobolevNormAt, torusRealPairing]

/-- B2 physical energy identity generalized to smooth periodic forcing. -/
theorem weightedEnergyIdentity_smoothT
    {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f) (hfp : IsPeriodicOn univ f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => (periodicSobolevENorm 1 (fun x => w.velocity (s, x))).toReal ^ 2)
      (-2 * ν * gradientSqT (fun x => w.velocity (t, x)) -
        2 * ν * laplacianSqT (fun x => w.velocity (t, x)) +
        2 * periodicPairing (fun x => advection (lift (fun y => w.velocity (t, y))) 0 x)
          (laplacian (fun x => w.velocity (t, x))) +
        2 * periodicPairing (fun x => w.velocity (t, x)) (fun x => f (t, x)) -
        2 * periodicPairing (fun x => f (t, x)) (laplacian (fun x => w.velocity (t, x)))) t := by
  have ht' := Ioo_subset_Ico_self ht
  have hz : SmoothPeriodicT (fun x => w.velocity (t, x)) :=
    ⟨classical_velocity_slice_contDiff w ht', w.velocity_periodic t ht'⟩
  have hb : SmoothPeriodicT (fun x => f (t, x)) :=
    ⟨hf.comp (contDiff_const.prodMk contDiff_id), hfp t (mem_univ t)⟩
  have hn : SmoothPeriodicT (fun x => convectionFieldT w.velocity (t, x)) :=
    ⟨advection_spatial_contDiff hz.1, advection_spatial_periodic hz.2⟩
  obtain ⟨G, hG⟩ := exists_periodicDatum_smooth 1 hz.1 hz.2
  obtain ⟨F, hF⟩ := exists_force_datum hf hfp 1 t
  obtain ⟨N, hN⟩ := exists_convection_datum w 1 ht'
  have hd := inhomogeneousEnergyIdentity_smoothT w hf ht hG hF hN
  rw [torusGradientNormAt_one_sqT w ht', torusRealPairing_one_eqT hz hb hG hF,
    torusRealPairing_one_eqT hz hn hG hN] at hd
  have hzero : periodicPairing (fun x => w.velocity (t, x))
      (fun x => convectionFieldT w.velocity (t, x)) = 0 :=
    periodicPairing_convection_zeroT _ hz (w.divergence t ht')
  rw [hzero, T20.periodicPairing_comm (laplacian (fun x => w.velocity (t, x)))
    (fun x => f (t, x)),
    T20.periodicPairing_comm (laplacian (fun x => w.velocity (t, x)))
      (fun x => convectionFieldT w.velocity (t, x))] at hd
  have he : (fun x => convectionFieldT w.velocity (t, x)) =
      (fun x => advection (lift (fun y => w.velocity (t, y))) 0 x) := rfl
  rw [he] at hd
  convert hd using 1 <;> ring

/-- Shift-compatible enstrophy inequality, with no norm-bridge premises. -/
theorem enstrophy_differential_smoothT
    {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f)
    (hfp : IsPeriodicOn univ f) (hν : 0 < ν)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    let Cν := (2 * convectionConstT) ^ 4 / (ν / 2) ^ 3 + (1 + ν) + (1 + 2 / ν)
    deriv (fun q => (periodicSobolevENorm 1 (fun x => w.velocity (q, x))).toReal ^ 2) t +
      ν * (periodicSobolevENorm 2 (fun x => w.velocity (t, x))).toReal ^ 2 ≤
    Cν * (1 + (periodicSobolevENorm 1 (fun x => w.velocity (t, x))).toReal ^ 2) ^ 3 +
      Cν * lTwoSqT (fun x => f (t, x)) := by
  have hz : SmoothPeriodicT (fun x => w.velocity (t, x)) :=
    ⟨classical_velocity_slice_contDiff w (Ioo_subset_Ico_self ht),
      w.velocity_periodic t (Ioo_subset_Ico_self ht)⟩
  have hb : Continuous (fun x => f (t, x)) := (hf.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hC : 0 ≤ convectionConstT := by
    have := cutoffGradBound_nonneg
    have := NSFormalization.Section4.A05.gradientL6Const_pos
    unfold convectionConstT velocitySixConstT
    positivity
  have hOne := periodicHOne_bridgeT hz.1 hz.2
  have hconv := convection_boundT _ hz (periodicGradient_bridgeT hz.1).le
  rw [← hOne] at hconv
  have hP := abs_pairing_carrier_leT _ _ hz.1.continuous hb
  have hQ := abs_pairing_carrier_leT _ _ hb (contDiff_laplacian hz.1).continuous
  have h := weighted_cubic_assemblyT hν hC
    (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)
    hOne (periodicHTwo_bridgeT hz.1 hz.2).le
    (weightedEnergyIdentity_smoothT w hf hfp ht).deriv hconv
    ((le_abs_self _).trans hP) ((neg_le_abs _).trans hQ)
  change _ ≤ _ + (1 + 2 / ν) * lTwoSqT (fun x => f (t, x)) at h
  dsimp only
  have hA : 0 ≤ (2 * convectionConstT) ^ 4 / (ν / 2) ^ 3 + (1 + ν) := by positivity
  have hB : 0 ≤ 1 + 2 / ν := by positivity
  have hY : 0 ≤ (1 + (periodicSobolevENorm 1 (fun x => w.velocity (t, x))).toReal ^ 2) ^ 3 := by positivity
  have hF : 0 ≤ lTwoSqT (fun x => f (t, x)) := sq_nonneg _
  nlinarith only [h, mul_nonneg hA hF, mul_nonneg hB hY]

/-- Compact dissipation integrals agree in real and extended-real carriers. -/
theorem periodicHTwo_lintegral_eqT {ν T s : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T)
    (hs0 : 0 ≤ s) (hsT : s < T) :
    (∫⁻ t in Ico (0 : ℝ) s, periodicSobolevENorm 2 (fun x => w.velocity (t, x)) ^ 2) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..s,
        (periodicSobolevENorm 2 (fun x => w.velocity (t, x))).toReal ^ 2) := by
  have hi : IntegrableOn (fun t =>
      (periodicSobolevENorm 2 (fun x => w.velocity (t, x))).toReal ^ 2)
      (Icc (0 : ℝ) s) := ((continuousOn_periodicSobolevEnergyT w 2).mono
        (fun t ht => ⟨ht.1, ht.2.trans_lt hsT⟩)).integrableOn_Icc
  rw [intervalIntegral.integral_of_le hs0, ← integral_Ico_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hi.mono_set Ico_subset_Icc_self)
      (ae_of_all _ (fun t => sq_nonneg _))]
  apply setLIntegral_congr_fun measurableSet_Ico
  intro t ht
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨ht.1, ht.2.trans hsT⟩
  have hn := periodicSobolevENorm_ne_top_smooth 2
    (classical_velocity_slice_contDiff w ht') (w.velocity_periodic t ht')
  dsimp only
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hn]

/-- One dissipation bound and one positive window precede both shift and datum. -/
theorem uniform_periodicHTwo_running_boundT (ν : ℝ) (hν : 0 < ν)
    (f : SpaceTimeField) (hf : MemForceT f) (S : ℝ) (hS : 0 ≤ S)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ d > 0, d ≤ 1 ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a : SpatialField, periodicSobolevENorm 1 a ≤ K →
      ∀ T : ℝ, ∀ w : ClassicalSolutionT ν a (timeShiftT t₀ f) T,
      ∀ s : ℝ, 0 ≤ s → s < T → s ≤ d →
        (∫⁻ t in Ico (0 : ℝ) s,
          periodicSobolevENorm 2 (fun x => w.velocity (t, x)) ^ 2) ≤ ENNReal.ofReal B := by
  let C := (2 * convectionConstT) ^ 4 / (ν / 2) ^ 3 + (1 + ν) + (1 + 2 / ν)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨d, hd, M, hM, hb⟩ :=
    NSFormalization.Section4.A04.enstrophy_uniform_barrier_and_dissipation hν hC
      (sq_nonneg K.toReal) (sq_nonneg (forceL2CapT f S).toReal)
  let D := min d 1
  let B := (K.toReal ^ 2 + C * (1 + M) ^ 3 * D +
    C * (forceL2CapT f S).toReal ^ 2 * D) / ν
  have hD : 0 < D := lt_min hd zero_lt_one
  have hM0 : 0 ≤ M := by rw [hM]; nlinarith [sq_nonneg K.toReal]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨D, hD, min_le_right _ _, B, hB, ?_⟩
  intro t₀ ht₀ a ha T w s hs0 hsT hsD
  let Y := fun t => (periodicSobolevENorm 1 (fun x => w.velocity (t, x))).toReal ^ 2
  let Z := fun t => (periodicSobolevENorm 2 (fun x => w.velocity (t, x))).toReal ^ 2
  have hsub : Icc (0 : ℝ) s ⊆ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hsT⟩
  have hcY : ContinuousOn Y (Icc (0 : ℝ) s) := by
    simpa only [Nat.cast_one] using (continuousOn_periodicSobolevEnergyT w 1).mono hsub
  have hcZ : ContinuousOn Z (Icc (0 : ℝ) s) :=
    (continuousOn_periodicSobolevEnergyT w 2).mono hsub
  have hinit : Y 0 ≤ K.toReal ^ 2 := by
    have he : (fun x => w.velocity (0, x)) = a := funext w.initial
    dsimp [Y]
    rw [he]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hK ha) 2
  have hdY : ∀ t ∈ Ioo (0 : ℝ) s, DifferentiableAt ℝ Y t := by
    intro t ht
    simpa only [Nat.cast_one] using
      differentiableAt_periodicSobolevEnergyT w 1 ⟨ht.1, ht.2.trans hsT⟩
  have hi : ∀ t ∈ Ioo (0 : ℝ) s,
      deriv Y t + ν * Z t ≤ C * (1 + Y t) ^ 3 + C * (forceL2CapT f S).toReal ^ 2 := by
    intro t ht
    have he := enstrophy_differential_smoothT w
      (timeShiftT_contDiff hf.1 t₀) (timeShiftT_periodic hf.2.1 t₀)
      hν ⟨ht.1, ht.2.trans hsT⟩
    exact he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (timeShiftT_lTwoSq_le_forceL2CapT hf hS ht₀
        ⟨ht.1.le, ht.2.le.trans (hsD.trans (min_le_right _ _))⟩) hC.le))
  have hh := hb 0 s Y Z hs0 (hsD.trans (min_le_left _ _))
    (by simpa only [zero_add] using hcY)
    (by simpa only [zero_add] using hdY)
    (fun t _ => sq_nonneg _) hinit (fun t _ => sq_nonneg _)
    (by simpa only [zero_add] using hcZ.integrableOn_Icc (μ := volume))
    (by simpa only [zero_add] using hi)
  have hreal : (∫ t in (0 : ℝ)..s, Z t) ≤ B := by
    have hh' : (∫ t in (0 : ℝ)..s, Z t) ≤
        (K.toReal ^ 2 + C * (1 + M) ^ 3 * s +
          C * (forceL2CapT f S).toReal ^ 2 * s) / ν := by
      simpa only [zero_add] using hh.2
    apply hh'.trans
    dsimp [B]
    gcongr
  rw [periodicHTwo_lintegral_eqT w hs0 hsT]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The common running bound passes to a possibly maximal endpoint. -/
theorem uniform_periodicHTwo_endpoint_boundT (ν : ℝ) (hν : 0 < ν)
    (f : SpaceTimeField) (hf : MemForceT f) (S : ℝ) (hS : 0 ≤ S)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ d > 0, ∃ B : ℝ, 0 ≤ B ∧
      ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a : SpatialField, periodicSobolevENorm 1 a ≤ K →
      ∀ R : ℝ, 0 < R → R ≤ d →
      ∀ (u : SpaceTimeField) (p : NSFormalization.Section4.A02.SpaceTimeScalar),
        SolvesBelowT ν a (timeShiftT t₀ f) R u p →
          squaredHTwoIntegralT R u ≤ ENNReal.ofReal B := by
  obtain ⟨d, hd, _, B, hB, hb⟩ := uniform_periodicHTwo_running_boundT ν hν f hf S hS K hK
  refine ⟨d, hd, B, hB, ?_⟩
  intro t₀ ht₀ a ha R hR hRd u p hu
  have heq (s : ℝ) (hs : s ≤ R) :
      (∫⁻ t in Ico (0 : ℝ) s, periodicSobolevENorm 2 (fun x => u (t, x)) ^ 2) =
        ∫⁻ t in Ico (0 : ℝ) s,
          ENNReal.ofReal ((periodicSobolevENorm 2 (fun x => u (t, x))).toReal ^ 2) := by
    apply setLIntegral_congr_fun measurableSet_Ico
    intro t ht
    dsimp only
    obtain ⟨w, hw, _⟩ := hu ((t + R) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hn : periodicSobolevENorm 2 (fun x => u (t, x)) ≠ ⊤ := by
      rw [← hw]
      have ht' : t ∈ Ico (0 : ℝ) ((t + R) / 2) := ⟨ht.1, by linarith [ht.2]⟩
      exact periodicSobolevENorm_ne_top_smooth 2 (classical_velocity_slice_contDiff w ht')
        (w.velocity_periodic t ht')
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hn]
  have he : (∫⁻ t in Ico (0 : ℝ) R,
      periodicSobolevENorm 2 (fun x => u (t, x)) ^ 2) ≤ ENNReal.ofReal B := by
    rw [heq R le_rfl]
    apply NSFormalization.Section4.A04.enstrophy_endpoint_lintegral
    intro s hs
    rw [← heq s hs.le]
    by_cases hs0 : 0 ≤ s
    · obtain ⟨w, hw, _⟩ := hu ((s + R) / 2) (by linarith) (by linarith)
      have h := hb t₀ ht₀ a ha _ w s hs0 (by linarith) (hs.le.trans hRd)
      simpa only [hw] using h
    · simp [Ico_eq_empty_of_le (le_of_not_ge hs0)]
  exact (lintegral_mono_set Ioo_subset_Ico_self).trans he

/-- Existing H³ energy estimate under the smooth force hypotheses used by Picard. -/
theorem periodicHThree_energy_smoothT {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T)
    (hf : ContDiff ℝ ∞ f) (hfp : IsPeriodicOn univ f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ d g : ℝ, 0 ≤ g ∧
      HasDerivAt (fun r => torusSobolevNormAt 3 w.velocity r ^ 2) d t ∧
      (1 / 2) * d + ν * g ^ 2 ≤
        torusPairingConstant 3 * torusSobolevNormAt 2 w.velocity t *
          torusSobolevNormAt 3 w.velocity t * g +
            torusSobolevNormAt 3 f t * torusSobolevNormAt 3 w.velocity t := by
  have ht' := Ioo_subset_Ico_self ht
  have hz := classical_velocity_slice_contDiff w ht'
  have hp := w.velocity_periodic t ht'
  obtain ⟨G, hG⟩ := exists_periodicDatum_smooth 3 hz hp
  obtain ⟨G1, hG1⟩ := exists_periodicDatum_smooth (3 + 1) hz hp
  obtain ⟨F, hF⟩ := exists_force_datum hf hfp 3 t
  obtain ⟨N, hN⟩ := exists_convection_datum w 3 ht'
  let g := torusGradientNormAt 3 w.velocity t
  refine ⟨-2 * ν * g ^ 2 + 2 * torusRealPairing G F - 2 * torusRealPairing G N,
    g, torusGradientNormAt_nonneg _ _ _, ?_, ?_⟩
  · exact energyIdentity_of_classical w hf 3 ht hG hF hN
  · have hforce : torusRealPairing G F ≤
        torusSobolevNormAt 3 f t * torusSobolevNormAt 3 w.velocity t := by
      rw [torusSobolevNormAt_eq hG, torusSobolevNormAt_eq hF, mul_comm]
      exact torusRealPairing_le G F
    have hconv := (neg_le_abs (torusRealPairing G N)).trans
      (torusPairingBound_slice (m := 3) le_rfl hz hp hG hG1 hN)
    change -torusRealPairing G N ≤
      torusPairingConstant 3 * torusSobolevNormAt 2 w.velocity t *
        torusSobolevNormAt 3 w.velocity t * g at hconv
    linarith

/-- Finite H² dissipation bounds H³ for any smooth periodic force. -/
theorem periodicHThree_bound_smoothT {ν S : ℝ} (hν : 0 < ν)
    {a : SpatialField} {f u : SpaceTimeField}
    {p : NSFormalization.Section4.A02.SpaceTimeScalar}
    (hf : ContDiff ℝ ∞ f) (hfp : IsPeriodicOn univ f)
    (hu : SolvesBelowT ν a f S u p) (hfin : squaredHTwoIntegralT S u ≠ ⊤) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ t ∈ Ico (0 : ℝ) S, periodicSobolevENorm 3 (fun x => u (t, x)) ≤ K := by
  obtain ⟨F, hFs, hF⟩ := exists_smooth_forceDatumPath hf hfp 3
  have hc : Continuous (fun t => torusSobolevNormAt 3 f t) := by
    apply hFs.continuous.norm.congr
    intro t
    exact (torusSobolevNormAt_eq (hF t)).symm
  let B := ∫ r in (0 : ℝ)..S, torusSobolevNormAt 3 f r
  refine ⟨ENNReal.ofReal ((torusSobolevNormAt 3 u 0 + B) *
    Real.exp ((torusPairingConstant 3) ^ 2 / (4 * ν) * (squaredHTwoIntegralT S u).toReal)),
    ENNReal.ofReal_ne_top, ?_⟩
  intro t ht
  obtain ⟨w, hw, _⟩ := hu ((t + S) / 2) (by linarith [ht.1, ht.2]) (by linarith [ht.2])
  have ht' : t ∈ Ico (0 : ℝ) ((t + S) / 2) := ⟨ht.1, by linarith [ht.2]⟩
  have hbS : (t + S) / 2 ≤ S := by linarith [ht.2]
  have h := torusGronwallChain (C := torusPairingConstant 3) (ν := ν)
    (Kbnd := (squaredHTwoIntegralT S u).toReal) (Bbnd := B)
    (y := fun r => torusSobolevNormAt 3 w.velocity r)
    (a := fun r => torusSobolevNormAt 2 w.velocity r)
    (b := fun r => torusSobolevNormAt 3 f r)
    hν (continuousOn_torusSobolevNormAt_velocity w 3)
    (fun r => torusSobolevNormAt_nonneg _ _ _)
    (continuousOn_torusSobolevNormAt_velocity w 2) hc.continuousOn
    (fun r => torusSobolevNormAt_nonneg _ _ _)
    (fun r hr => by
      have hh := running_hTwo_integral_le w hw hbS hfin hr
      rw [hw]
      exact hh)
    (fun r hr => intervalIntegral.integral_mono_interval le_rfl hr.1
      (hr.2.le.trans hbS) (ae_of_all _ (fun r => torusSobolevNormAt_nonneg _ _ _))
      (hc.intervalIntegrable 0 S))
    (fun r hr => periodicHThree_energy_smoothT w hf hfp hr) t ht'
  have hn := periodicSobolevENorm_ne_top_smooth 3
    (classical_velocity_slice_contDiff w ht') (w.velocity_periodic t ht')
  rw [hw] at hn h
  rw [← ENNReal.ofReal_toReal hn]
  exact ENNReal.ofReal_le_ofReal h

/-- H³ Picard and gluing realize a strictly larger horizon for shifted forces. -/
theorem shifted_horizon_extensionT {ν R t₀ : ℝ} (hν : 0 < ν)
    {a : SpatialField} {f u : SpaceTimeField}
    {p : NSFormalization.Section4.A02.SpaceTimeScalar}
    (hf : MemForceT f) (ht₀ : 0 ≤ t₀) (hR : 0 < R)
    (hu : SolvesBelowT ν a (timeShiftT t₀ f) R u p)
    (hfin : squaredHTwoIntegralT R u ≠ ⊤) :
    ∃ T : ℝ, R < T ∧ Nonempty (ClassicalSolutionT ν a (timeShiftT t₀ f) T) := by
  obtain ⟨K, hK, hbound⟩ := periodicHThree_bound_smoothT hν
    (timeShiftT_contDiff hf.1 t₀) (timeShiftT_periodic hf.2.1 t₀) hu hfin
  let M := fun m : ℕ => forceSobolevENormT 1 (m : ℝ) f
  obtain ⟨d, hd, hloc⟩ := periodicQuantitativeLocalInputH3 ν hν K hK M
    (fun m => forceSobolevENormT_ne_top hf m 1)
  let b := max 0 (R - d / 2)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hbR : b < R := max_lt hR (by linarith)
  have hRb : R < b + d := by have := le_max_right 0 (R - d / 2); dsimp [b]; linarith
  obtain ⟨w, hw, _⟩ := hu ((b + R) / 2) (by linarith) (by linarith)
  have hb : b ∈ Ico (0 : ℝ) ((b + R) / 2) := ⟨hb0, by linarith⟩
  obtain ⟨v, _⟩ := hloc (fun x => w.velocity (b, x))
    (velocitySlice_mem_initialClassT w hb)
    (by rw [hw]; exact hbound b ⟨hb0, hbR⟩)
    (timeShiftT b (timeShiftT t₀ f))
    (timeShiftT_contDiff (timeShiftT_contDiff hf.1 t₀) b)
    (timeShiftT_periodic (timeShiftT_periodic hf.2.1 t₀) b)
    (fun m => (forceSobolevENormT_timeShift_le (m : ℝ) _ b hb0).trans
      (forceSobolevENormT_timeShift_le (m : ℝ) f t₀ ht₀))
  obtain ⟨v', _, _⟩ := glueClassicalSolutionT hν w hb v
    (by linarith : (b + R) / 2 < b + d)
  exact ⟨b + d, hRb, ⟨v'⟩⟩

/-- Maximal gluing only needs positive local existence, smoothness and periodicity. -/
theorem exists_maximal_smoothT {ν : ℝ} (hν : 0 < ν)
    {a : SpatialField} (ha : a ∈ initialClassT) {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (hfp : IsPeriodicOn univ f) :
    ∃ (u : SpaceTimeField) (p : NSFormalization.Section4.A02.SpaceTimeScalar),
      IsMaximalPeriodicSolution ν a f u p := by
  obtain ⟨T, _, w, _⟩ := exists_classical_of_picard ν hν a ha f hf hfp
  have hpos : 0 < maximalLifespanT ν a f :=
    (ENNReal.ofReal_pos.mpr w.horizon_pos).trans_le (lifespan_ge_of_horizon w)
  have hflow : 0 < NSFormalization.Paper1.PeriodicLifespan.lifespan ν a f := by
    rwa [← maximalLifespanT_eq_lifespan]
  obtain ⟨M⟩ :=
    NSFormalization.Paper1.PeriodicLocalLifespan.exists_maximal_periodic_solution_of_lifespan_pos
      hν hflow
  refine ⟨M.velocity, M.pressure, hpos, ?_⟩
  intro S hS hSL
  have hSE : ENNReal.ofReal S < M.endpoint := by
    rw [M.endpoint_eq_lifespan, ← maximalLifespanT_eq_lifespan]
    exact hSL
  exact ⟨ofNormalizedFlow (M.flow S hS hSE) (M.normalized S hS hSE),
    M.velocity_eq S hS hSE, M.pressure_eq S hS hSE⟩

end NSFormalization.Section3.T11
