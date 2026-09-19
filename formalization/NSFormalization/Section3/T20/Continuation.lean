import NSFormalization.Section3.T20.H1Energy

/-!
# T20 unit U11 — the continuation bound (`03-torus.tex:486-500`)

For the zero initial datum and a force `g ∈ F_T` with `ρ < c ν`, the squared
`H²` time integral of the *full* velocity `u` of a classical torus solution
splits along the orthogonal constant/mean-zero Fourier decomposition,

`∫₀ˢ ‖u(t)‖²_{H²} dt = ∫₀ˢ (|m(t)|² + ‖v(t)‖²_{H²}) dt
   ≤ S ρ² + Ccriterion ν⁻² ∫₀^∞ ‖h(t)‖²₂ dt < ∞`,

which is the `continuationBound` field of `CriticalRegularityTAPI` verbatim, at
`c = criticalSmallnessH1` (lane 432) and `Ccriterion = hTwoConst² · CH1`.

## Route

* §1 **The orthogonal mode decomposition.**  Removing the spatial mean deletes
  the `k = 0` Fourier coefficient and changes nothing else, and the order-`2`
  Bessel weight at `k = 0` is `1`; so frequency by frequency
  `freqEnergyT 2 u k t = freqEnergyT 2 v k t + (k = 0 ? |m(t)|² : 0)`, whence
  `‖u(t)‖²_{H²} = |m(t)|² + ‖v(t)‖²_{H²}`.  This is the one genuinely new torus
  ingredient of the unit.
* §2 Continuity of the two profiles on the lifespan: `‖v(·)‖²_{H²}` is the
  difference of T11's continuous `H²` profile and the smooth `|m(·)|²`, and
  `‖∇v(·)‖²₂` is squeezed between `0` and T11's continuous `H¹` profile, which
  vanishes at `t = 0` because the initial datum is zero.
* §3 The mean-free force is itself a member of `F_T`, so lane 312's
  `force_coefficient_path` at order `0` makes `‖h(·)‖²₂` continuous with compact
  support; order-zero Parseval identifies it with the datum norm and makes
  `∫₀^∞‖h‖²₂` a finite real integral.
* §4 **The `H²` budget.**  `‖v‖²_{H²} ≤ hTwoConst²‖Δv‖²₂` (T12
  `hTwo_le_laplacian`) turns U10b's `eq:H1energy` into
  `(‖∇v‖²₂)' + (ν/hTwoConst²)‖v‖²_{H²} ≤ CH1 ν⁻¹‖h‖²₂`; integrating it on
  `[a,b] ⊂ (0,T)` (`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`)
  and letting `a → 0⁺`, where `‖∇v(a)‖²₂ → 0`, gives
  `∫₀^b ‖v‖²_{H²} ≤ hTwoConst²·CH1·ν⁻²∫₀^∞‖h‖²₂` for every `b < T`.
* §5 Assembly: the mean part is bounded by `S ρ²` through U2's `meanBound`, the
  mean-zero part by §4 after exhausting `Ioo 0 S` by the `Ioo 0 b`
  (`setLIntegral_iUnion_of_directed`), and both bounds are finite.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
override, no named goal input.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators

/-! ## §0  Extended-real bookkeeping -/

/-- The canonical field writes the squared extended norms with a real exponent;
this is the `ℕ`-power spelling `squaredHTwoIntegralT` uses. -/
theorem enorm_rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

/-! ## §1  The orthogonal constant/mean-zero mode decomposition -/

/-- **Removing the spatial mean deletes exactly the zero mode.**  Off `k = 0`
the Fourier coefficients of `z - ∫z` are those of `z`; at `k = 0` they vanish. -/
theorem coeff_meanZeroPart {z : SpatialField} (hs : ContDiff ℝ ∞ z)
    (hp : IsPeriodicSpatial z) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((meanZeroPartT z x i : ℝ) : ℂ)) k =
      if k = 0 then 0 else periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum 0 hs hp
  have hc : periodicFourierCoeff (fun x ↦ ((meanZeroPartT z x i : ℝ) : ℂ)) k =
      periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k -
        periodicFourierCoeff (fun _ : Space ↦ ((meanT z i : ℝ) : ℂ)) k := by
    simpa only [meanZeroPartT, PiLp.sub_apply, Complex.ofReal_sub] using
      periodicFourierCoeff_sub (hA.integrable_component i) (integrable_const _) k
  rw [hc, periodicFourierCoeff_const]
  by_cases hk : k = 0
  · subst hk
    rw [periodicFourierCoeff_zero_eq_mean_component hA.2.1 i]
    simp
  · simp [hk]

/-- The zero-mode coefficient of the velocity slice is the data-defined mean. -/
theorem velocityCoeffT_zero_eq_meanPath {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) :
    velocityCoeffT w.velocity i 0 t = ((meanPathT g t i : ℝ) : ℂ) := by
  have hs : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) :=
    classical_velocity_slice_contDiff w ht
  have hp : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t ht
  obtain ⟨A, hA⟩ := smooth_periodic_datum 0 hs hp
  have hmean : meanPathT g t = meanT (fun x ↦ w.velocity (t, x)) := by
    have hm := periodicMeanReductionAPI.mean_formula ν hν (fun _ : Space ↦ (0 : Space))
      zero_mem_initialClassT g hg T w t ht
    simpa [meanPathT, velocityMeanT, galileanMeanT, meanT_const] using hm.symm
  rw [velocityCoeffT, periodicFourierCoeff_zero_eq_mean_component hA.2.1 i, hmean]

/-- The mean-free velocity has the velocity's coefficients off the zero mode and
no zero mode. -/
theorem velocityCoeffT_meanFreeVelocity {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    velocityCoeffT (meanFreeVelocity g w.velocity) i k t =
      if k = 0 then 0 else velocityCoeffT w.velocity i k t := by
  have hs : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) :=
    classical_velocity_slice_contDiff w ht
  have hp : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t ht
  have hveq := meanFreeVelocity_slice_eq hν hg w ht
  have hfun : (fun x ↦ ((meanFreeVelocity g w.velocity (t, x) i : ℝ) : ℂ)) =
      fun x ↦ ((meanZeroPartT (fun y ↦ w.velocity (t, y)) x i : ℝ) : ℂ) := by
    funext x
    rw [congrFun hveq x]
  rw [velocityCoeffT, hfun, coeff_meanZeroPart hs hp i k]
  rfl

/-- The squared Euclidean norm as the component sum of complexified entries. -/
theorem norm_sq_eq_sum_complex (m : Space) :
    ‖m‖ ^ 2 = ∑ i : Fin 3, ‖((m i : ℝ) : ℂ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [Real.norm_eq_abs]

/-- **The orthogonal mode decomposition, frequency by frequency.**  The order-`2`
Bessel weight at `k = 0` is `1`, so the deleted zero mode contributes exactly
`|m(t)|²`. -/
theorem freqEnergyT_two_split {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (k : PeriodicFrequency) :
    freqEnergyT 2 w.velocity k t =
      freqEnergyT 2 (meanFreeVelocity g w.velocity) k t +
        (if k = 0 then ‖meanPathT g t‖ ^ 2 else 0) := by
  by_cases hk : k = 0
  · subst hk
    have hw : periodicFrequencyWeight (0 : PeriodicFrequency) = 1 := by
      simp [periodicFrequencyWeight]
    have hv : ∀ i : Fin 3,
        velocityCoeffT (meanFreeVelocity g w.velocity) i 0 t = 0 := by
      intro i
      rw [velocityCoeffT_meanFreeVelocity hν hg w ht i 0]
      simp
    have hu : ∀ i : Fin 3,
        velocityCoeffT w.velocity i 0 t = ((meanPathT g t i : ℝ) : ℂ) :=
      fun i ↦ velocityCoeffT_zero_eq_meanPath hν hg w ht i
    simp only [freqEnergyT, hw, Real.one_rpow, one_mul]
    simp only [hv, hu, norm_zero]
    rw [norm_sq_eq_sum_complex (meanPathT g t)]
    simp
  · have hv : ∀ i : Fin 3,
        velocityCoeffT (meanFreeVelocity g w.velocity) i k t =
          velocityCoeffT w.velocity i k t := by
      intro i
      rw [velocityCoeffT_meanFreeVelocity hν hg w ht i k]
      simp [hk]
    simp only [freqEnergyT, hv, hk, ↓reduceIte, add_zero]

/-- **`‖u(t)‖²_{H²} = |m(t)|² + ‖v(t)‖²_{H²}`** on the lifespan. -/
theorem torusSobolevNormAt_two_sq_split {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    torusSobolevNormAt 2 w.velocity t ^ 2 =
      ‖meanPathT g t‖ ^ 2 +
        torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 := by
  have hus : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) :=
    classical_velocity_slice_contDiff w ht
  have hup : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t ht
  have hreg := reductionRegular ν hν g hg T w t ht
  have hvSP : SmoothPeriodicT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := hreg.2.1
  obtain ⟨A, hA⟩ := smooth_periodic_datum (2 : ℝ) hus hup
  obtain ⟨B, hB⟩ := smooth_periodic_datum (2 : ℝ) hvSP.1 hvSP.2
  have hsu : HasSum (fun k ↦ freqEnergyT 2 w.velocity k t) (‖A‖ ^ 2) :=
    hasSum_freqEnergyT hA
  have hsv : HasSum (fun k ↦ freqEnergyT 2 (meanFreeVelocity g w.velocity) k t)
      (‖B‖ ^ 2) := hasSum_freqEnergyT hB
  have hsm : HasSum
      (fun k : PeriodicFrequency ↦ if k = 0 then ‖meanPathT g t‖ ^ 2 else 0)
      (‖meanPathT g t‖ ^ 2) := hasSum_ite_eq 0 _
  have hsum : HasSum (fun k ↦ freqEnergyT 2 w.velocity k t)
      (‖B‖ ^ 2 + ‖meanPathT g t‖ ^ 2) :=
    (hsv.add hsm).congr_fun fun k ↦ freqEnergyT_two_split hν hg w ht k
  have huniq : ‖A‖ ^ 2 = ‖B‖ ^ 2 + ‖meanPathT g t‖ ^ 2 := hsu.unique hsum
  rw [torusSobolevNormAt_eq hA, torusSobolevNormAt_eq hB, huniq]
  ring

/-! ## §2  Continuity of the two time profiles -/

/-- The zero field is an order-`s` datum of the zero periodic field. -/
theorem zero_isPeriodicDatum (s : ℝ) :
    IsPeriodicDatum s (fun _ : Space ↦ (0 : Space)) 0 := by
  refine ⟨fun _ _ ↦ rfl, integrable_zero _ _ _, fun i k ↦ ?_⟩
  have hz : (fun x : Space ↦ (((0 : Space) i : ℝ) : ℂ)) = fun _ : Space ↦ (0 : ℂ) := by
    funext x
    norm_num
  rw [hz, periodicFourierCoeff_const]
  simp

/-- The data-defined mean path is smooth, hence continuous. -/
theorem contDiff_meanPathT {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    ContDiff ℝ ∞ (meanPathT g) :=
  Transport.contDiff_galileanMeanT hg.1

/-- **`t ↦ ‖v(t)‖²_{H²}` is continuous on the lifespan**: by §1 it is the
difference of T11's continuous `H²` velocity profile and the smooth `|m(·)|²`. -/
theorem continuousOn_meanFreeHTwoSq {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T) :
    ContinuousOn
      (fun t ↦ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
      (Ico (0 : ℝ) T) := by
  have hc1 : ContinuousOn (fun t ↦ torusSobolevNormAt (2 : ℝ) w.velocity t ^ 2)
      (Ico (0 : ℝ) T) := by
    have h := (continuousOn_torusSobolevNormAt_velocity w 2).pow 2
    rwa [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at h
  have hc2 : Continuous (fun t ↦ ‖meanPathT g t‖ ^ 2) :=
    ((contDiff_meanPathT hg).continuous.norm).pow 2
  refine (hc1.sub hc2.continuousOn).congr fun t ht ↦ ?_
  have h := torusSobolevNormAt_two_sq_split hν hg w ht
  show torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 =
    torusSobolevNormAt (2 : ℝ) w.velocity t ^ 2 - ‖meanPathT g t‖ ^ 2
  linarith

/-- `‖∇v(t)‖²₂ ≤ ‖u(t)‖²_{H¹}`: the homogeneous order-one weight `|2πk|²` is
dominated by the inhomogeneous Bessel weight `1 + |2πk|²`. -/
theorem gradientSqT_le_hOneSq {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (g : SpaceTimeField) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) :
    gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ≤
      torusSobolevNormAt 1 w.velocity t ^ 2 := by
  have hus : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) :=
    classical_velocity_slice_contDiff w ht
  have hup : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t ht
  obtain ⟨A, hA⟩ := smooth_periodic_datum (1 : ℝ) hus hup
  rw [gradientSqT_meanFreeVelocity_eq_tsum hus hup, torusSobolevNormAt_sq_eq_tsum hA]
  refine (summable_h1FreqEnergy w ht).tsum_le_tsum (fun k ↦ ?_)
    (hasSum_freqEnergyT hA).summable
  have hone : periodicFrequencyWeight k ^ (1 : ℝ) = periodicFrequencyWeight k :=
    Real.rpow_one _
  show periodicAngularFrequencySq k * _ ≤ periodicFrequencyWeight k ^ (1 : ℝ) * _
  rw [hone]
  exact mul_le_mul_of_nonneg_right (angularFrequencySq_le_periodicFrequencyWeight k)
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)

/-- The `H^m` profile of the velocity vanishes at the zero initial datum. -/
theorem torusSobolevNormAt_initial {ν T : ℝ} {f : SpaceTimeField} (s : ℝ)
    (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) f T) :
    torusSobolevNormAt s w.velocity 0 = 0 := by
  have hz : (fun x ↦ w.velocity (0, x)) = fun _ : Space ↦ (0 : Space) := by
    funext x
    exact w.initial x
  have hd : IsPeriodicDatum s (fun x ↦ w.velocity (0, x)) 0 := by
    rw [hz]
    exact zero_isPeriodicDatum s
  rw [torusSobolevNormAt_eq hd, norm_zero]

/-- **`‖∇v(a)‖²₂ → 0` as `a → 0⁺`**, squeezed between `0` and the continuous
`H¹` velocity profile, which vanishes at the zero initial datum. -/
theorem tendsto_gradientSqT_nhdsGT_zero {ν T : ℝ} {g : SpaceTimeField}
    (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T) :
    Filter.Tendsto
      (fun s ↦ gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (s, x)))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
  have hIco : Ico (0 : ℝ) T ∈ nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ≤ nhds (0 : ℝ))
        (Iio_mem_nhds w.horizon_pos)] with x hx1 hx2
    exact ⟨le_of_lt hx1, hx2⟩
  have hmono : nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ≤ nhdsWithin (0 : ℝ) (Ico (0 : ℝ) T) :=
    nhdsWithin_le_iff.2 hIco
  have hM : Filter.Tendsto (fun s ↦ torusSobolevNormAt (1 : ℝ) w.velocity s ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by
    have hc : ContinuousOn (fun s ↦ torusSobolevNormAt (1 : ℝ) w.velocity s ^ 2)
        (Ico (0 : ℝ) T) := by
      have h := (continuousOn_torusSobolevNormAt_velocity w 1).pow 2
      rwa [Nat.cast_one] at h
    have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) T := ⟨le_rfl, w.horizon_pos⟩
    have := (hc 0 h0).tendsto
    rw [torusSobolevNormAt_initial 1 w] at this
    simpa using this.mono_left hmono
  refine squeeze_zero' (Filter.Eventually.of_forall fun s ↦ ?_) ?_ hM
  · exact sq_nonneg _
  · filter_upwards [hIco] with s hs
    exact gradientSqT_le_hOneSq w g hs

/-! ## §3  The mean-free force and its `L²` time budget -/

/-- **The mean-free force of a test force is again a test force.**  Off the time
support of `g` every slice vanishes, hence so does its mean. -/
theorem memForceT_meanFreeForce {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    MemForceT (meanFreeForce g) := by
  obtain ⟨hs, hp, K, hK, hKpos, hsupp⟩ := hg
  have hmean : ContDiff ℝ ∞ (forceMeanT g) := MeanIdentity.forceMeanT_contDiff hs
  refine ⟨hs.sub (hmean.comp contDiff_fst), ?_, K, hK, hKpos, ?_⟩
  · intro t _ x j
    show g (t, x + coordinateVector j) - forceMeanT g t = g (t, x) - forceMeanT g t
    rw [hp t (mem_univ _) x j]
  · refine closure_minimal (fun q hq ↦ ?_) (hK.isClosed.prod isClosed_univ)
    refine ⟨?_, mem_univ _⟩
    by_contra hKq
    have hzero : ∀ x : Space, g (q.1, x) = 0 := by
      intro x
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      exact hKq (hsupp hx).1
    have hmz : forceMeanT g q.1 = 0 := by
      have hfun : (fun x ↦ g (q.1, x)) = fun _ : Space ↦ (0 : Space) := funext hzero
      show meanT (fun x ↦ g (q.1, x)) = 0
      rw [hfun]
      exact meanT_const (0 : Space)
    have hgq : g q = 0 := by
      have h := hzero q.2
      rwa [Prod.mk.eta] at h
    exact hq (by show g q - forceMeanT g q.1 = 0; rw [hgq, hmz, sub_zero])

/-- **The order-zero datum path of the mean-free force.**  Lane 312's
`force_coefficient_path` supplies a globally continuous, compactly supported
order-`0` path; order-zero Parseval identifies `‖h(t)‖₂` with its norm. -/
theorem exists_meanFreeForce_profile {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    ∃ G : ℝ → PeriodicSobolev ((0 : ℕ) : ℝ),
      Continuous G ∧ (∀ q : ℝ≥0∞, MemLp G q forceTimeMeasure) ∧
        ∀ t : ℝ,
          periodicLpENorm 2 (fun x ↦ meanFreeForce g (t, x)) = ‖G t‖ₑ ∧
            lTwoSqT (fun x ↦ meanFreeForce g (t, x)) = ‖G t‖ ^ 2 := by
  have hmf : MemForceT (meanFreeForce g) := memForceT_meanFreeForce hg
  obtain ⟨G, hGd, hGc, -, -, -, hGq⟩ := force_coefficient_path hmf 0
  refine ⟨G, hGc, hGq, fun t ↦ ?_⟩
  have hs : ContDiff ℝ ∞ (fun x ↦ meanFreeForce g (t, x)) :=
    hmf.1.comp (contDiff_const.prodMk contDiff_id)
  have hp : IsPeriodicSpatial (fun x ↦ meanFreeForce g (t, x)) := hmf.2.1 t (mem_univ _)
  have hL : periodicLpENorm 2 (fun x ↦ meanFreeForce g (t, x)) = ‖G t‖ₑ := by
    have h0 : periodicSobolevENorm (((0 : ℕ) : ℝ)) (fun x ↦ meanFreeForce g (t, x))
        = ‖G t‖ₑ := periodicSobolevENorm_eq_datum (hGd t)
    rw [Nat.cast_zero] at h0
    show eLpNorm (torusLift (fun x ↦ meanFreeForce g (t, x))) 2 periodicTorusMeasure = _
    rw [← sobolevENorm_zero_eq hs hp, h0]
  refine ⟨hL, ?_⟩
  show (periodicLpENorm 2 (fun x ↦ meanFreeForce g (t, x))).toReal ^ 2 = _
  rw [hL, toReal_enorm]

/-- `‖h(·)‖²₂` is continuous on all of `ℝ`. -/
theorem continuous_forceLTwoSq {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    Continuous (fun t ↦ lTwoSqT (fun x ↦ meanFreeForce g (t, x))) := by
  obtain ⟨G, hGc, -, hG⟩ := exists_meanFreeForce_profile hg
  have h : Continuous (fun t ↦ ‖G t‖ ^ 2) := hGc.norm.pow 2
  exact h.congr fun t ↦ (hG t).2.symm

/-- `‖h(·)‖²₂` is integrable over the positive times. -/
theorem integrableOn_forceLTwoSq {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    IntegrableOn (fun t ↦ lTwoSqT (fun x ↦ meanFreeForce g (t, x))) (Ioi (0 : ℝ))
      volume := by
  obtain ⟨G, -, hGq, hG⟩ := exists_meanFreeForce_profile hg
  have h : Integrable (fun t ↦ ‖G t‖ ^ 2) forceTimeMeasure :=
    (hGq ((2 : ℕ) : ℝ≥0∞)).integrable_norm_pow (by norm_num)
  refine (h.congr ?_ : Integrable _ forceTimeMeasure)
  exact Filter.Eventually.of_forall fun t ↦ (hG t).2.symm

/-- `‖h(t)‖²₂ ≥ 0`. -/
theorem forceLTwoSq_nonneg (g : SpaceTimeField) (t : ℝ) :
    0 ≤ lTwoSqT (fun x ↦ meanFreeForce g (t, x)) := sq_nonneg _

/-- **`∫₀^∞‖h‖²₂` is the finite real integral of the profile.** -/
theorem meanFreeForceLTwoSqIntegral_eq {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    meanFreeForceLTwoSqIntegral (meanFreeForce g) =
      ENNReal.ofReal
        (∫ t in Ioi (0 : ℝ), lTwoSqT (fun x ↦ meanFreeForce g (t, x))) := by
  obtain ⟨G, -, -, hG⟩ := exists_meanFreeForce_profile hg
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_forceLTwoSq hg)
    (Filter.Eventually.of_forall fun t ↦ forceLTwoSq_nonneg g t)]
  show (∫⁻ t, (periodicLpENorm 2 (fun x ↦ meanFreeForce g (t, x))) ^ (2 : ℝ)
      ∂(volume.restrict (Ioi (0 : ℝ)))) = _
  refine lintegral_congr fun t ↦ ?_
  rw [(hG t).1, enorm_rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    (hG t).2]

/-- The `L²` time budget of the mean-free force is finite. -/
theorem meanFreeForceLTwoSqIntegral_ne_top {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤ := by
  rw [meanFreeForceLTwoSqIntegral_eq hg]
  exact ENNReal.ofReal_ne_top

/-! ## §4  The `H²` budget on `(0,b)` -/

/-- `03-torus.tex:492-500`: the absolute constant of the squared-`H²`
continuation bound.  `hTwoConst = 1 + 1/(4π²)` is T12's mean-zero
`H²`/Laplacian comparison constant and `CH1 = 2` is U10b's `eq:H1energy`
constant. -/
def Ccriterion : ℝ := hTwoConst ^ 2 * CH1

theorem Ccriterion_pos : 0 < Ccriterion := by
  have h1 : (0 : ℝ) < hTwoConst := hTwoConst_pos
  have h2 : (0 : ℝ) < CH1 := CH1_pos
  unfold Ccriterion
  positivity

/-- `‖v(t)‖²_{H²} ≤ hTwoConst² ‖Δv(t)‖²₂` on the lifespan (T12
`hTwo_le_laplacian` in real form). -/
theorem meanFreeHTwoSq_le_laplacianSq {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 ≤
      hTwoConst ^ 2 *
        laplacianSqT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := by
  have hreg := reductionRegular ν hν g hg T w t ht
  have hvSP : SmoothPeriodicT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := hreg.2.1
  have hvMZ : IsMeanZeroT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := hreg.1
  have hlap : periodicLpENorm 2
      (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x))) ≠ ⊤ :=
    hreg.2.2.2.2.2.2.2.2.2.2
  have hle := hTwo_le_laplacian _ hvSP hvMZ
  have hfin : ENNReal.ofReal hTwoConst * periodicLpENorm 2
      (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlap
  have hreal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hTwoConst_pos.le] at hreal
  have hnn : (0 : ℝ) ≤ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t :=
    ENNReal.toReal_nonneg
  have hrhs : (0 : ℝ) ≤ hTwoConst *
      (periodicLpENorm 2
        (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x)))).toReal :=
    mul_nonneg hTwoConst_pos.le ENNReal.toReal_nonneg
  have hsq := mul_self_le_mul_self hnn hreal
  have hlapEq : laplacianSqT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) =
      (periodicLpENorm 2
        (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x)))).toReal ^ 2 := rfl
  rw [hlapEq]
  nlinarith [hsq, hnn, hrhs]

/-- **The `H²` budget on every `(0,b)` strictly inside the lifespan.**
Integrating U10b's `eq:H1energy` after replacing `ν‖Δv‖²₂` by
`(ν/hTwoConst²)‖v‖²_{H²}`, and letting the left endpoint tend to `0`, where
`‖∇v‖²₂ → 0` because the initial datum vanishes. -/
theorem meanFreeHTwoSq_integral_le {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT)
    (hsmall : criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν))
    (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T) {b : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) T) :
    (∫ t in Ioo (0 : ℝ) b,
        torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) ≤
      Ccriterion * (ν⁻¹) ^ 2 *
        ∫ t in Ioi (0 : ℝ), lTwoSqT (fun x ↦ meanFreeForce g (t, x)) := by
  have hc2 : (0 : ℝ) < hTwoConst ^ 2 := pow_pos hTwoConst_pos 2
  have hIcb : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) T := fun x hx ↦ ⟨hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have hNcont : ContinuousOn
      (fun t ↦ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
      (Icc (0 : ℝ) b) := (continuousOn_meanFreeHTwoSq hν hg w).mono hIcb
  have hNnn : ∀ t : ℝ, 0 ≤ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 :=
    fun t ↦ sq_nonneg _
  have hFnn : ∀ s : ℝ,
      0 ≤ gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (s, x)) := by
    intro s
    unfold gradientSqT
    exact sq_nonneg _
  have hHcont : Continuous (fun t ↦ lTwoSqT (fun x ↦ meanFreeForce g (t, x))) :=
    continuous_forceLTwoSq hg
  have hHIoi := integrableOn_forceLTwoSq hg
  set HFtot : ℝ := ∫ t in Ioi (0 : ℝ), lTwoSqT (fun x ↦ meanFreeForce g (t, x))
    with hHFdef
  -- the pointwise differential inequality, with `‖Δv‖²₂` replaced by `‖v‖²_{H²}`
  have hstep : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun s ↦ gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (s, x)))
          (deriv (fun s ↦ gradientSqT
            (fun x ↦ meanFreeVelocity g w.velocity (s, x))) t) t ∧
        deriv (fun s ↦ gradientSqT
            (fun x ↦ meanFreeVelocity g w.velocity (s, x))) t ≤
          CH1 * ν⁻¹ * lTwoSqT (fun x ↦ meanFreeForce g (t, x)) -
            (ν / hTwoConst ^ 2) *
              torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 := by
    intro t ht
    obtain ⟨E', hE', hle⟩ := hOneEnergy ν hν g hg hsmall T w t ht
    have hd : deriv (fun s ↦ gradientSqT
        (fun x ↦ meanFreeVelocity g w.velocity (s, x))) t = E' := hE'.deriv
    refine ⟨by rw [hd]; exact hE', ?_⟩
    rw [hd]
    have hNL := meanFreeHTwoSq_le_laplacianSq hν hg w ⟨ht.1.le, ht.2⟩
    have habs : (ν / hTwoConst ^ 2) *
        torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 ≤
        ν * laplacianSqT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc2]
      nlinarith [hNL, hν.le]
    linarith
  -- the integrated inequality on `[a,b]`
  have hkey : ∀ a ∈ Ioo (0 : ℝ) b,
      (∫ t in a..b, torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) ≤
        (hTwoConst ^ 2 / ν) *
          (gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (a, x)) +
            CH1 * ν⁻¹ * HFtot) := by
    intro a ha
    have hab : a ≤ b := ha.2.le
    have hIab : Icc a b ⊆ Ioo (0 : ℝ) T := fun x hx ↦
      ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
    have hFcont : ContinuousOn
        (fun s ↦ gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (s, x)))
        (Icc a b) := fun x hx ↦ ((hstep x (hIab hx)).1.continuousAt).continuousWithinAt
    have hNab : ContinuousOn
        (fun t ↦ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
        (Icc a b) := hNcont.mono (Icc_subset_Icc ha.1.le le_rfl)
    have hφcont : ContinuousOn
        (fun t ↦ CH1 * ν⁻¹ * lTwoSqT (fun x ↦ meanFreeForce g (t, x)) -
          (ν / hTwoConst ^ 2) *
            torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) (Icc a b) :=
      (continuousOn_const.mul hHcont.continuousOn).sub (continuousOn_const.mul hNab)
    have hmain := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hFcont
      (fun x hx ↦ ((hstep x (hIab (Ioo_subset_Icc_self hx))).1).hasDerivWithinAt)
      hφcont.integrableOn_Icc
      (fun x hx ↦ (hstep x (hIab (Ioo_subset_Icc_self hx))).2)
    have hHii : IntervalIntegrable
        (fun t ↦ lTwoSqT (fun x ↦ meanFreeForce g (t, x))) volume a b :=
      hHcont.intervalIntegrable a b
    have hNii : IntervalIntegrable
        (fun t ↦ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
        volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      exact hNab.integrableOn_Icc
    rw [intervalIntegral.integral_sub (hHii.const_mul _) (hNii.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmain
    have hHle : (∫ t in a..b, lTwoSqT (fun x ↦ meanFreeForce g (t, x))) ≤ HFtot := by
      rw [intervalIntegral.integral_of_le hab, hHFdef]
      refine setIntegral_mono_set hHIoi
        (Filter.Eventually.of_forall fun t ↦ forceLTwoSq_nonneg g t) ?_
      have hsub : Ioc a b ≤ Ioi (0 : ℝ) := fun x hx ↦ lt_trans ha.1 hx.1
      exact hsub.eventuallyLE
    have hνc : (0 : ℝ) < ν / hTwoConst ^ 2 := div_pos hν hc2
    have hFb := hFnn b
    have hCH1 : (0 : ℝ) < CH1 := CH1_pos
    have hνi : (0 : ℝ) < ν⁻¹ := inv_pos.2 hν
    have hprod : CH1 * ν⁻¹ *
        (∫ t in a..b, lTwoSqT (fun x ↦ meanFreeForce g (t, x))) ≤
        CH1 * ν⁻¹ * HFtot :=
      mul_le_mul_of_nonneg_left hHle (by positivity)
    have hstep2 : (ν / hTwoConst ^ 2) *
        (∫ t in a..b, torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) ≤
        gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (a, x)) +
          CH1 * ν⁻¹ * HFtot := by
      linarith [hmain, hFb, hprod]
    have hpos : (0 : ℝ) ≤ hTwoConst ^ 2 / ν := le_of_lt (div_pos hc2 hν)
    have h1 := mul_le_mul_of_nonneg_left hstep2 hpos
    have h2 : (hTwoConst ^ 2 / ν) *
        ((ν / hTwoConst ^ 2) *
          (∫ t in a..b,
            torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)) =
        ∫ t in a..b, torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 := by
      field_simp [hTwoConst_pos.ne']
    linarith [h1, h2.symm.le, h2.le]
  -- the primitive at the left endpoint tends to zero
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hNcont
  have hprim : Filter.Tendsto
      (fun a ↦ ∫ t in (0 : ℝ)..a,
        torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hbnd : ∀ᶠ a in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
        (∫ t in (0 : ℝ)..a,
          torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) ≤ C * a := by
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ≤ nhds (0 : ℝ))
          (Iio_mem_nhds hb.1)] with a ha1 ha2
      have hsub : Set.uIoc (0 : ℝ) a ⊆ Icc (0 : ℝ) b := by
        rw [Set.uIoc_of_le (le_of_lt ha1)]
        exact fun x hx ↦ ⟨hx.1.le, hx.2.trans ha2.le⟩
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C) (f := fun t ↦ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
        (a := (0 : ℝ)) (b := a) (fun x hx ↦ hC x (hsub hx))
      have habs : |∫ t in (0 : ℝ)..a,
          torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2| ≤ C * |a - 0| := by
        simpa [Real.norm_eq_abs] using hnorm
      have : |a - 0| = a := by
        rw [sub_zero, abs_of_pos ha1]
      rw [this] at habs
      exact (le_abs_self _).trans habs
    refine squeeze_zero' ?_ hbnd ?_
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact intervalIntegral.integral_nonneg ha.le fun t _ ↦ hNnn t
    · have : Filter.Tendsto (fun a : ℝ ↦ C * a) (nhds 0) (nhds (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
  have hF0 : Filter.Tendsto
      (fun a ↦ gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (a, x)))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := tendsto_gradientSqT_nhdsGT_zero w
  have hR : Filter.Tendsto
      (fun a ↦ (∫ t in (0 : ℝ)..a,
            torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) +
          (hTwoConst ^ 2 / ν) *
            (gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (a, x)) +
              CH1 * ν⁻¹ * HFtot))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds (0 + (hTwoConst ^ 2 / ν) * (0 + CH1 * ν⁻¹ * HFtot))) :=
    hprim.add (tendsto_const_nhds.mul (hF0.add tendsto_const_nhds))
  have hev : ∀ᶠ a in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      (∫ t in Ioo (0 : ℝ) b,
          torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) ≤
        (∫ t in (0 : ℝ)..a,
            torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) +
          (hTwoConst ^ 2 / ν) *
            (gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (a, x)) +
              CH1 * ν⁻¹ * HFtot) := by
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ≤ nhds (0 : ℝ))
        (Iio_mem_nhds hb.1)] with a ha1 ha2
    have hNii0 : IntervalIntegrable
        (fun t ↦ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
        volume 0 a := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha1.le]
      exact (hNcont.mono (Icc_subset_Icc le_rfl ha2.le)).integrableOn_Icc
    have hNiiab : IntervalIntegrable
        (fun t ↦ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
        volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le ha2.le]
      exact (hNcont.mono (Icc_subset_Icc ha1.le le_rfl)).integrableOn_Icc
    have hadd := intervalIntegral.integral_add_adjacent_intervals hNii0 hNiiab
    have hIoo : (∫ t in Ioo (0 : ℝ) b,
        torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) =
        ∫ t in (0 : ℝ)..b,
          torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 := by
      rw [intervalIntegral.integral_of_le hb.1.le, integral_Ioc_eq_integral_Ioo]
    rw [hIoo, ← hadd]
    have := hkey a ⟨ha1, ha2⟩
    linarith
  have hfinal := le_of_tendsto_of_tendsto tendsto_const_nhds hR hev
  have hνne : ν ≠ 0 := ne_of_gt hν
  calc (∫ t in Ioo (0 : ℝ) b,
        torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
      ≤ 0 + (hTwoConst ^ 2 / ν) * (0 + CH1 * ν⁻¹ * HFtot) := hfinal
    _ = Ccriterion * (ν⁻¹) ^ 2 * HFtot := by
        unfold Ccriterion
        field_simp
        ring

/-! ## §5  `continuationBound` -/

/-- The extended-norm form of §1: `‖u(t)‖²_{H²} = |m(t)|² + ‖v(t)‖²_{H²}` in
`ℝ≥0∞`, exactly the two integrands of `squaredHTwoIntegralT` and
`meanModeCriterionIntegral`. -/
theorem sobolevENorm_two_sq_split {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    periodicSobolevENorm 2 (fun x ↦ w.velocity (t, x)) ^ 2 =
      ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ) +
        periodicSobolevENorm 2
          (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ^ (2 : ℝ) := by
  have hus : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) :=
    classical_velocity_slice_contDiff w ht
  have hup : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t ht
  have hreg := reductionRegular ν hν g hg T w t ht
  have hvSP : SmoothPeriodicT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := hreg.2.1
  obtain ⟨A, hA⟩ := smooth_periodic_datum (2 : ℝ) hus hup
  obtain ⟨B, hB⟩ := smooth_periodic_datum (2 : ℝ) hvSP.1 hvSP.2
  have hsplit := torusSobolevNormAt_two_sq_split hν hg w ht
  rw [torusSobolevNormAt_eq hA, torusSobolevNormAt_eq hB] at hsplit
  have hA2 : ‖A‖ₑ ^ 2 = ENNReal.ofReal (‖A‖ ^ 2) := by
    rw [← ofReal_norm]
    rw [← ENNReal.ofReal_pow (norm_nonneg A)]
  have hB2 : ‖B‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖B‖ ^ 2) := by
    rw [enorm_rpow_two, ← ofReal_norm]
    rw [← ENNReal.ofReal_pow (norm_nonneg B)]
  have hm2 : ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ) =
      ENNReal.ofReal (‖meanPathT g t‖ ^ 2) := by
    rw [enorm_rpow_two]
    rw [← ENNReal.ofReal_pow (norm_nonneg (meanPathT g t))]
  rw [periodicSobolevENorm_eq_datum hA, periodicSobolevENorm_eq_datum hB,
    hA2, hB2, hm2, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), hsplit]

/-- The mean-zero integrand as a real square, on the lifespan. -/
theorem sobolevENorm_two_meanFree_sq {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    periodicSobolevENorm 2
        (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ^ (2 : ℝ) =
      ENNReal.ofReal
        (torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) := by
  have hreg := reductionRegular ν hν g hg T w t ht
  have hvSP : SmoothPeriodicT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := hreg.2.1
  obtain ⟨B, hB⟩ := smooth_periodic_datum (2 : ℝ) hvSP.1 hvSP.2
  rw [torusSobolevNormAt_eq hB, enorm_rpow_two, periodicSobolevENorm_eq_datum hB,
    ← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg B)]

/-- **T20 U11, `03-torus.tex:486-500`.**  For the zero initial datum and
`g ∈ F_T` with `ρ < c ν`, on every `0 < S ≤ T` the squared `H²` time integral of
the velocity splits orthogonally, is bounded by `S ρ² + Ccriterion ν⁻² ∫₀^∞‖h‖²₂`,
and that bound is finite.  This is the `continuationBound` field of
`CriticalRegularityTAPI` verbatim, at `c = criticalSmallnessH1` and
`Ccriterion = hTwoConst² · CH1`. -/
theorem continuationBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ (S : ℝ), 0 < S → S ≤ T →
            squaredHTwoIntegralT S w.velocity =
                meanModeCriterionIntegral S g w.velocity ∧
              meanModeCriterionIntegral S g w.velocity ≤
                ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ∧
              ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤ := by
  intro ν hν g hg hsmall T w S hS hST
  have hCpos : (0 : ℝ) ≤ Ccriterion * (ν⁻¹) ^ 2 := by
    have := Ccriterion_pos
    positivity
  -- (1) the orthogonal mode identity
  have hid : squaredHTwoIntegralT S w.velocity =
      meanModeCriterionIntegral S g w.velocity := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    exact sobolevENorm_two_sq_split hν hg w ⟨ht.1.le, lt_of_lt_of_le ht.2 hST⟩
  -- (2) the two halves of the bound
  have hPmeas : Measurable
      (fun t ↦ ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ)) := by
    simp only [enorm_rpow_two]
    exact ((ENNReal.continuous_ofReal.comp
      (contDiff_meanPathT hg).continuous.norm).measurable).pow_const 2
  have hsplitInt : meanModeCriterionIntegral S g w.velocity =
      (∫⁻ t in Ioo (0 : ℝ) S, ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ)) +
        ∫⁻ t in Ioo (0 : ℝ) S,
          periodicSobolevENorm 2
            (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ^ (2 : ℝ) :=
    lintegral_add_left hPmeas _
  have hmeanle : (∫⁻ t in Ioo (0 : ℝ) S,
      ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ)) ≤
      ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) := by
    calc (∫⁻ t in Ioo (0 : ℝ) S, ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ))
        ≤ ∫⁻ _ in Ioo (0 : ℝ) S, criticalRho g ^ (2 : ℝ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          have hb := meanBound g hg t ht.1.le
          exact ENNReal.rpow_le_rpow (hb.1.trans hb.2) (by norm_num)
      _ = criticalRho g ^ (2 : ℝ) * ENNReal.ofReal S := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
      _ = ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) := mul_comm _ _
  -- the exhausting sequence for the open right endpoint
  set bb : ℕ → ℝ := fun n ↦ S - S / ((n : ℝ) + 2) with hbbdef
  have hbbpos : ∀ n : ℕ, 0 < bb n := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : S / ((n : ℝ) + 2) < S := by
      rw [div_lt_iff₀ h2]
      nlinarith
    simp only [hbbdef]
    linarith
  have hbblt : ∀ n : ℕ, bb n < S := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : 0 < S / ((n : ℝ) + 2) := div_pos hS h2
    simp only [hbbdef]
    linarith
  have hbbmono : Monotone bb := by
    intro i j hij
    have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hle : ((i : ℝ) + 2) ≤ ((j : ℝ) + 2) := by
      have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
      linarith
    have hd : S / ((j : ℝ) + 2) ≤ S / ((i : ℝ) + 2) := by
      gcongr
    simp only [hbbdef]
    linarith
  have hunion : Ioo (0 : ℝ) S = ⋃ n : ℕ, Ioo (0 : ℝ) (bb n) := by
    refine Subset.antisymm (fun t ht ↦ ?_)
      (iUnion_subset fun n ↦ Ioo_subset_Ioo le_rfl (hbblt n).le)
    obtain ⟨n, hn⟩ := exists_nat_gt (S / (S - t))
    refine mem_iUnion.2 ⟨n, ht.1, ?_⟩
    have hSt : (0 : ℝ) < S - t := sub_pos.2 ht.2
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hn2 : S / (S - t) < (n : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ hSt] at hn2
    have hfrac : S / ((n : ℝ) + 2) < S - t := by
      rw [div_lt_iff₀ h2]
      nlinarith
    simp only [hbbdef]
    linarith
  have hQle : (∫⁻ t in Ioo (0 : ℝ) S,
      periodicSobolevENorm 2
        (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
        meanFreeForceLTwoSqIntegral (meanFreeForce g) := by
    have hdir : Directed (· ⊆ ·) (fun n : ℕ ↦ Ioo (0 : ℝ) (bb n)) := by
      intro i j
      exact ⟨max i j, Ioo_subset_Ioo le_rfl (hbbmono (le_max_left i j)),
        Ioo_subset_Ioo le_rfl (hbbmono (le_max_right i j))⟩
    rw [hunion, setLIntegral_iUnion_of_directed _ hdir]
    refine iSup_le fun n ↦ ?_
    have hbn : bb n ∈ Ioo (0 : ℝ) T :=
      ⟨hbbpos n, lt_of_lt_of_le (hbblt n) hST⟩
    have hsub : Icc (0 : ℝ) (bb n) ⊆ Ico (0 : ℝ) T := fun x hx ↦
      ⟨hx.1, lt_of_le_of_lt hx.2 hbn.2⟩
    have hNint : IntegrableOn
        (fun t ↦ torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2)
        (Ioo (0 : ℝ) (bb n)) volume :=
      (((continuousOn_meanFreeHTwoSq hν hg w).mono hsub).integrableOn_Icc).mono_set
        Ioo_subset_Icc_self
    calc (∫⁻ t in Ioo (0 : ℝ) (bb n),
          periodicSobolevENorm 2
            (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ^ (2 : ℝ))
        = ∫⁻ t in Ioo (0 : ℝ) (bb n),
            ENNReal.ofReal
              (torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
          exact sobolevENorm_two_meanFree_sq hν hg w
            ⟨ht.1.le, lt_trans ht.2 hbn.2⟩
      _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) (bb n),
            torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal hNint
            (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2 *
            ∫ t in Ioi (0 : ℝ), lTwoSqT (fun x ↦ meanFreeForce g (t, x))) :=
          ENNReal.ofReal_le_ofReal
            (meanFreeHTwoSq_integral_le hν hg hsmall w hbn)
      _ = ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
            meanFreeForceLTwoSqIntegral (meanFreeForce g) := by
          rw [meanFreeForceLTwoSqIntegral_eq hg, ← ENNReal.ofReal_mul hCpos]
  -- (3) finiteness
  have hρ : criticalRho g ≠ ⊤ := ne_top_of_lt hsmall
  have hne : ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
      ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
        meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (meanFreeForceLTwoSqIntegral_ne_top hg)⟩
    rw [enorm_rpow_two]
    exact ENNReal.pow_ne_top hρ
  refine ⟨hid, ?_, hne⟩
  rw [hsplitInt]
  exact add_le_add hmeanle hQle

end NSFormalization.Section3.T20
