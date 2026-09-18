import NSFormalization.Section3.T10.FourierCalculus
import NSFormalization.Section3.T12.MeanZeroCalculus
import NSFormalization.Paper1.PeriodicForceSpace
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Continuous coefficient paths of smooth periodic forces. -/
noncomputable section
namespace NSFormalization.Section3.T10
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NavierStokes.PeriodicIntegration (spatialPartial)
open scoped ContDiff ENNReal BigOperators Topology

 theorem memForceT_iff_isTestForce (f : SpaceTimeField) :
    MemForceT f ↔ NSFormalization.Paper1.PeriodicForceSpace.IsTestForce f := by
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2⟩, fun h ↦ ⟨h.smooth, h.periodic, h.time_support⟩⟩

 theorem memLp_torusLift_vector {v : SpatialField} (hv : Continuous v) (q : ℝ≥0∞) :
    MemLp (torusLift v) q periodicTorusMeasure := by
  apply MemLp.of_eval_piLp
  intro i
  exact (NSFormalization.Paper1.memLp_torusLift
    (Complex.continuous_ofReal.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hv)) q).re

 theorem smooth_periodic_datum (s : ℝ) {v : SpatialField}
    (hs : ContDiff ℝ ∞ v) (hp : IsPeriodicSpatial v) :
    ∃ A : PeriodicSobolev s, IsPeriodicDatum s v A := by
  let a : PeriodicVectorData := WithLp.toLp 2 (fun i ↦
    NSFormalization.Paper1.smoothPeriodicWeightedFourierLp s (fun x ↦ (v x i : ℂ))
      (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs))
      (fun x j ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hp x j)))
  have ha (i : Fin 3) (k : PeriodicFrequency) :
      a i k = periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k := by
    simp only [a, NSFormalization.Paper1.smoothPeriodicWeightedFourierLp,
      periodicFrequencyWeight_eq_paper1]
  have hr : a ∈ realPeriodicSubmodule := by
    intro i k
    rw [ha, ha, periodicFourierCoeff_real_neg]
    have hw : periodicFrequencyWeight (-k) = periodicFrequencyWeight k := by
      simp [periodicFrequencyWeight]
    rw [hw]
    simp
  exact ⟨⟨a, hr⟩, hp, (memLp_torusLift_vector hs.continuous 1).integrable (by norm_num), ha⟩

 theorem periodicSobolevENorm_eq {s : ℝ} {v : SpatialField} {A : PeriodicSobolev s}
    (hA : IsPeriodicDatum s v A) : periodicSobolevENorm s v = ‖A‖ₑ := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨A, hA⟩ le_rfl
  · apply le_iInf
    intro B
    rw [datum_unique s v B.1 A B.2 hA]

 theorem norm_scalar_datum_nat (m : ℕ) {v : SpatialField} {A : PeriodicSobolev (m : ℝ)}
    (hs : ContDiff ℝ ∞ v) (hA : IsPeriodicDatum (m : ℝ) v A) (i : Fin 3) :
    ‖A.1 i‖ = Real.sqrt (NSFormalization.Paper1.periodicIntegerEnergy m
      (fun x ↦ (v x i : ℂ))) := by
  have hc : ContDiff ℝ ∞ (fun x ↦ (v x i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)
  have hp : NavierStokes.PeriodicIntegration.UnitPeriods (fun x ↦ (v x i : ℂ)) :=
    fun x j ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hA.1 x j)
  have he : A.1 i = NSFormalization.Paper1.smoothPeriodicWeightedFourierLp (m : ℝ)
      (fun x ↦ (v x i : ℂ)) hc hp := by
    ext k
    simpa only [NSFormalization.Paper1.smoothPeriodicWeightedFourierLp,
      periodicFrequencyWeight_eq_paper1] using hA.2.2 i k
  rw [he, NSFormalization.Paper1.norm_smoothPeriodicWeightedFourierLp,
    NSFormalization.Paper1.periodicSobolevNorm,
    NSFormalization.Paper1.periodicSobolevSq_nat m (hc.of_le (by simp)) hp]

 theorem datum_sub {s : ℝ} {v w : SpatialField} {A B : PeriodicSobolev s}
    (hA : IsPeriodicDatum s v A) (hB : IsPeriodicDatum s w B) :
    IsPeriodicDatum s (v - w) (A - B) := by
  refine ⟨fun x j ↦ by simp only [Pi.sub_apply, hA.1 x j, hB.1 x j],
    hA.2.1.sub hB.2.1, ?_⟩
  intro i k
  change A.1 i k - B.1 i k = _
  rw [hA.2.2, hB.2.2, ← smul_sub]
  congr 1
  simpa only [Pi.sub_apply, PiLp.sub_apply, Complex.ofReal_sub] using
    (periodicFourierCoeff_sub (hA.integrable_component i) (hB.integrable_component i) k).symm

 theorem continuous_datum_path (m : ℕ) {f : SpaceTimeField}
    (hs : ContDiff ℝ ∞ f) (G : ℝ → PeriodicSobolev (m : ℝ))
    (hG : ∀ t, IsPeriodicDatum (m : ℝ) (fun x ↦ f (t, x)) (G t)) : Continuous G := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro t
  change Filter.Tendsto _ _ _
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs' : ContDiff ℝ ∞ (fun z : SpaceTime ↦ f z - f (t, z.2)) :=
    hs.sub (hs.comp (contDiff_const.prodMk contDiff_snd))
  have hc : Continuous (fun u ↦ Real.sqrt (NSFormalization.Paper1.periodicIntegerEnergy m
      (fun x ↦ ((f (u, x) - f (t, x)) i : ℂ)))) := Real.continuous_sqrt.comp
    (NSFormalization.Paper1.continuous_periodicIntegerEnergy_time m
      (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs')))
  have he (u : ℝ) : ‖(G u).1 i - (G t).1 i‖ =
      Real.sqrt (NSFormalization.Paper1.periodicIntegerEnergy m
        (fun x ↦ ((f (u, x) - f (t, x)) i : ℂ))) :=
    norm_scalar_datum_nat m (hs'.comp (contDiff_const.prodMk contDiff_id))
      (datum_sub (hG u) (hG t)) i
  have hc' : Continuous (fun u ↦ ‖(G u).1 i - (G t).1 i‖) := by
    simpa only [he] using hc
  have ht := hc'.continuousAt (x := t)
  simpa only [ContinuousAt, sub_self, norm_zero] using ht

 theorem force_coefficient_path {f : SpaceTimeField} (hf : MemForceT f) (m : ℕ) :
    ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      (∀ t, IsPeriodicDatum (m : ℝ) (fun x ↦ f (t, x)) (G t)) ∧
      Continuous G ∧ HasCompactSupport G ∧ StronglyMeasurable G ∧
      IsPeriodicSobolevPath (m : ℝ) f G ∧
      (∀ q : ℝ≥0∞, MemLp G q forceTimeMeasure) := by
  have hex (t : ℝ) := smooth_periodic_datum (m : ℝ)
    (hf.1.comp (contDiff_const.prodMk contDiff_id)) (hf.2.1 t (mem_univ _))
  choose G hG using hex
  have hc := continuous_datum_path m hf.1 G hG
  obtain ⟨K, hK, _, hsupport⟩ := hf.2.2
  have hcompact : HasCompactSupport G := by
    apply HasCompactSupport.intro hK
    intro t ht
    have hz : (fun x ↦ f (t, x)) = 0 := by
      funext x
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      exact ht (hsupport hx).1
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    apply lp.ext
    funext k
    have hd : IsPeriodicDatum (m : ℝ) (fun x ↦ f (t, x)) (G t) := hG t
    rw [hz] at hd
    have hk := hd.2.2 i k
    simpa [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff,
      UnitAddTorus.mFourierCoeff, NSFormalization.Paper1.torusLift] using hk
  have hm : StronglyMeasurable G := hc.stronglyMeasurable_of_hasCompactSupport hcompact
  refine ⟨G, hG, hc, hcompact, hm, fun t _ ↦ hG t, ?_⟩
  intro q
  exact (hc.memLp_of_hasCompactSupport (μ := volume) (p := q) hcompact).mono_measure
    Measure.restrict_le_self

 theorem forceSobolevENormT_ne_top {f : SpaceTimeField} (hf : MemForceT f)
    (m : ℕ) (q : ℝ≥0∞) : forceSobolevENormT q (m : ℝ) f ≠ ⊤ := by
  obtain ⟨G, _, _, _, hm, hp, hq⟩ := force_coefficient_path hf m
  exact ne_top_of_le_ne_top (hq q).eLpNorm_ne_top
    (iInf_le_of_le ⟨G, hp, hm.aestronglyMeasurable⟩ le_rfl)

 theorem periodicFourierCoeff_component_derivative {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 1 v) (i j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (spatialPartial j (fun x ↦ (v x i : ℂ))) k =
      periodicDerivativeSymbol j k * periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k :=
  periodicFourierCoeff_fderiv
    (fun x l ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hp x l))
    (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)) j k

 theorem periodicFourierCoeff_component_decay {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ ∞ v) (i : Fin 3) (N : ℕ) :
    ∃ C : ℝ, ∀ k, periodicFrequencyWeight k ^ N *
      ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ≤ C :=
  periodicFourierCoeff_rapid_decay
    (fun x l ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hp x l))
    (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)) N

 theorem periodicFourierCoeff_component_laplacian {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 2 v) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ∑ j : Fin 3,
      spatialPartial j (spatialPartial j (fun y ↦ (v y i : ℂ))) x) k =
      (-periodicAngularFrequencySq k : ℂ) * periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k := by
  simpa only [periodicAngularFrequencySq, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat] using
    periodicFourierCoeff_laplacian (f := fun x ↦ (v x i : ℂ))
    (fun x l ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hp x l))
    (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)) k

 theorem periodicFourierCoeff_vector_gradient_sq {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 1 v) (k : PeriodicFrequency) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ‖periodicFourierCoeff (spatialPartial j (fun x ↦ (v x i : ℂ))) k‖ ^ 2) =
      periodicAngularFrequencySq k * ∑ i : Fin 3,
        ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact periodicFourierCoeff_gradient_sq
    (fun x l ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hp x l))
    (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)) k

 theorem gradientTensor_component {v : SpatialField} (hs : ContDiff ℝ 1 v)
    (i j : Fin 3) (x : Space) :
    (NSFormalization.Section3.T12.gradientTensor v x j i : ℂ) =
      spatialPartial j (fun y ↦ (v y i : ℂ)) x := by
  let L : Space →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)
  have h : HasFDerivAt (fun y ↦ (v y i : ℂ)) (L.comp (fderiv ℝ v x)) x :=
    L.hasFDerivAt.comp x (hs.differentiable (by norm_num) x).hasFDerivAt
  rw [spatialPartial, h.fderiv]
  rfl

 theorem memLp_gradientTensor {v : SpatialField} (hs : ContDiff ℝ ∞ v) :
    MemLp (torusLift (NSFormalization.Section3.T12.gradientTensor v)) 2 periodicTorusMeasure := by
  apply MemLp.of_eval_piLp
  intro j
  exact memLp_torusLift_vector
    ((hs.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const) 2

 theorem gradientTensor_parseval {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ ∞ v) :
    eLpNorm (torusLift (NSFormalization.Section3.T12.gradientTensor v)) 2 periodicTorusMeasure =
      ENNReal.ofReal (Real.sqrt (∑' k, periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ^ 2)) := by
  have hc (i j : Fin 3) : Continuous (spatialPartial j (fun x ↦ (v x i : ℂ))) :=
    (((Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)).fderiv_right
        (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hsum := hasSum_sum (s := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦
    hasSum_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
      NSFormalization.Paper1.hasSum_sq_periodicFourierCoeff _ (hc i j)))
  simp_rw [periodicFourierCoeff_vector_gradient_sq hp (hs.of_le (by simp))] at hsum
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (memLp_gradientTensor hs)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, hsum.tsum_eq]
  congr 2
  simp_rw [← NSFormalization.Paper1.integral_torusLift]
  have hi (i j : Fin 3) : Integrable
      (fun y ↦ ‖torusLift (spatialPartial j (fun x ↦ (v x i : ℂ))) y‖ ^ 2)
      periodicTorusMeasure :=
    (NSFormalization.Paper1.memLp_torusLift (hc i j) 2).integrable_norm_pow (by norm_num)
  change (∫ y, ‖torusLift (NSFormalization.Section3.T12.gradientTensor v) y‖ ^ 2 ∂periodicTorusMeasure) =
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ y,
      ‖torusLift (spatialPartial j (fun x ↦ (v x i : ℂ))) y‖ ^ 2 ∂periodicTorusMeasure
  simp_rw [← integral_finsetSum _ (fun j _ ↦ hi _ j)]
  rw [← integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
  congr 1
  funext y
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ‖NSFormalization.Section3.T12.gradientTensor v _ j i‖ ^ 2 = _
  rw [← Complex.norm_real, gradientTensor_component (hs.of_le (by simp))]
  rfl

 theorem angularFrequencySq_nonneg (k : PeriodicFrequency) :
    0 ≤ periodicAngularFrequencySq k := by
  unfold periodicAngularFrequencySq
  positivity

 theorem homogeneousDatumWeight_one (k : PeriodicFrequency) :
    homogeneousDatumWeight 1 k = Real.sqrt (periodicAngularFrequencySq k) := by
  unfold homogeneousDatumWeight
  split_ifs with hk
  · subst k
    simp [periodicAngularFrequencySq]
  · rw [Real.sqrt_eq_rpow]
    rfl

 theorem summable_angular_component {v : SpatialField} (hs : ContDiff ℝ ∞ v)
    (hp : IsPeriodicSpatial v) (i : Fin 3) :
    Summable (fun k ↦ periodicAngularFrequencySq k *
      ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ^ 2) := by
  have h := summable_weighted_periodicFourierCoeff
    (fun x j ↦ congrArg (fun y : Space ↦ (y i : ℂ)) (hp x j))
    (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)) 1
  simp only [Real.rpow_one] at h
  apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (angularFrequencySq_nonneg k) (sq_nonneg _)) _ h
  intro k
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change periodicAngularFrequencySq k ≤ 1 + periodicAngularFrequencySq k
  linarith

 theorem norm_sqrt_angular_smul_sq (k : PeriodicFrequency) (c : ℂ) :
    ‖Real.sqrt (periodicAngularFrequencySq k) • c‖ ^ 2 =
      periodicAngularFrequencySq k * ‖c‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (angularFrequencySq_nonneg k)]

 theorem smooth_homogeneous_datum_one {v : SpatialField}
    (hs : ContDiff ℝ ∞ v) (hp : IsPeriodicSpatial v) (hm : IsMeanZeroT v) :
    ∃ A : PeriodicSobolev 1, IsPeriodicHomogeneousDatum 1 v A := by
  let a (i : Fin 3) : PeriodicScalarData :=
    ⟨fun k ↦ Real.sqrt (periodicAngularFrequencySq k) •
      periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k,
      memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
        norm_sqrt_angular_smul_sq] using summable_angular_component hs hp i)⟩
  have hr : WithLp.toLp 2 a ∈ realPeriodicSubmodule := by
    intro i k
    change Real.sqrt (periodicAngularFrequencySq (-k)) •
      periodicFourierCoeff (fun x ↦ (v x i : ℂ)) (-k) =
      star (Real.sqrt (periodicAngularFrequencySq k) •
        periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k)
    rw [periodicFourierCoeff_real_neg]
    have hw : periodicAngularFrequencySq (-k) = periodicAngularFrequencySq k := by
      simp [periodicAngularFrequencySq]
    rw [hw]
    simp
  refine ⟨⟨WithLp.toLp 2 a, hr⟩, hp,
    (memLp_torusLift_vector hs.continuous 1).integrable (by norm_num), hm, ?_⟩
  intro i k
  rw [homogeneousDatumWeight_one]
  rfl

 theorem homogeneousENorm_one_eq {v : SpatialField}
    (hs : ContDiff ℝ ∞ v) (hp : IsPeriodicSpatial v) (hm : IsMeanZeroT v) :
    periodicHomogeneousENorm 1 v = ENNReal.ofReal (Real.sqrt
      (∑' k, periodicAngularFrequencySq k * ∑ i : Fin 3,
        ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ^ 2)) := by
  obtain ⟨A, hA⟩ := smooth_homogeneous_datum_one hs hp hm
  have he : periodicHomogeneousENorm 1 v = ‖A‖ₑ := by
    apply le_antisymm
    · exact iInf_le_of_le ⟨A, hA⟩ le_rfl
    · apply le_iInf
      intro B
      have hb : B.1 = A := by
        apply Subtype.ext
        apply WithLp.ofLp_injective 2
        funext i
        ext k
        rw [B.2.2.2.2 i k, hA.2.2.2 i k]
      rw [hb]
  rw [he, ← ofReal_norm]
  congr 1
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (tsum_nonneg (fun k ↦ mul_nonneg (angularFrequencySq_nonneg k)
    (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))))]
  change ‖A.1‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  have hn (i : Fin 3) : ‖A.1 i‖ ^ 2 = ∑' k, periodicAngularFrequencySq k *
      ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ^ 2 := by
    have hl := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (A.1 i)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hA.2.2.2,
      homogeneousDatumWeight_one, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, Real.sq_sqrt (angularFrequencySq_nonneg _)] using hl
  simp_rw [hn, Finset.mul_sum]
  exact (Summable.tsum_finsetSum (fun i _ ↦ summable_angular_component hs hp i)).symm

 theorem angular_meanZeroPart {v : SpatialField} (hs : ContDiff ℝ ∞ v)
    (hp : IsPeriodicSpatial v) (k : PeriodicFrequency) (i : Fin 3) :
    periodicAngularFrequencySq k *
      ‖periodicFourierCoeff (fun x ↦ (meanZeroPartT v x i : ℂ)) k‖ ^ 2 =
    periodicAngularFrequencySq k *
      ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ^ 2 := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum 0 hs hp
  have hc : periodicFourierCoeff (fun x ↦ (meanZeroPartT v x i : ℂ)) k =
      periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k -
        periodicFourierCoeff (fun _ : Space ↦ (meanT v i : ℂ)) k := by
    simpa only [meanZeroPartT, PiLp.sub_apply, Complex.ofReal_sub] using
      periodicFourierCoeff_sub (hA.integrable_component i) (integrable_const _) k
  rw [hc, periodicFourierCoeff_const]
  by_cases hk : k = 0
  · subst k
    simp [periodicAngularFrequencySq]
  · simp [hk]

 theorem gradient_eq_homogeneousENorm {v : SpatialField}
    (hs : ContDiff ℝ ∞ v) (hp : IsPeriodicSpatial v) :
    eLpNorm (torusLift (NSFormalization.Section3.T12.gradientTensor v)) 2 periodicTorusMeasure =
      periodicHomogeneousENorm 1 (meanZeroPartT v) := by
  have hm := (mean_decomposition v hp
    ((memLp_torusLift_vector hs.continuous 1).integrable (by norm_num))).2
  rw [homogeneousENorm_one_eq (v := meanZeroPartT v) (hs.sub contDiff_const)
    (fun x j ↦ by simp only [meanZeroPartT, hp x j]) hm, gradientTensor_parseval hp hs]
  congr 2
  apply tsum_congr
  intro k
  simp_rw [Finset.mul_sum, angular_meanZeroPart hs hp]

 theorem sobolevENorm_zero_eq {v : SpatialField} (hs : ContDiff ℝ ∞ v)
    (hp : IsPeriodicSpatial v) :
    periodicSobolevENorm 0 v = eLpNorm (torusLift v) 2 periodicTorusMeasure := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum 0 hs hp
  rw [periodicSobolevENorm_eq hA]
  exact parseval_forward v A hA (memLp_torusLift_vector hs.continuous 2)

 theorem energyENormT_eq (T : ℝ) (z : SpaceTimeField)
    (hs : ∀ t ∈ Ioo (0 : ℝ) T, ContDiff ℝ ∞ (fun x ↦ z (t, x)))
    (hp : IsPeriodicOn (Ioo (0 : ℝ) T) z) :
    energyENormT T z = coefficientEnergyENormT T z := by
  have h0 : energyEssSupT T z = coefficientEnergyEssSupT T z := by
    apply essSup_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (sobolevENorm_zero_eq (hs t ht) (hp t ht)).symm
  have h1 : energyGradientT T z = coefficientEnergyGradientT T z := by
    unfold energyGradientT coefficientEnergyGradientT
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    congr 1
    exact gradient_eq_homogeneousENorm (hs t ht) (hp t ht)
  exact congrArg₂ (· + ·) h0 h1

/-- Separated smooth profiles give concrete members of the force class. -/
theorem memForceT_time_smul {ρ : ℝ → ℝ} {v : SpatialField}
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi 0)
    (hv : ContDiff ℝ ∞ v) (hp : IsPeriodicSpatial v) :
    MemForceT (fun z : SpaceTime ↦ ρ z.1 • v z.2) := by
  refine ⟨(hρ.comp contDiff_fst).smul (hv.comp contDiff_snd), ?_,
    tsupport ρ, hc, hpos, ?_⟩
  · intro t _ x j
    dsimp
    rw [hp x j]
  · apply closure_minimal _ ((isClosed_tsupport ρ).prod isClosed_univ)
    intro z hz
    refine ⟨subset_tsupport ρ ?_, mem_univ _⟩
    intro h
    exact hz (by simp [h])

 theorem periodicFourierCoeff_gradientTensor {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 1 v) (i j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ (NSFormalization.Section3.T12.gradientTensor v x j i : ℂ)) k =
      periodicDerivativeSymbol j k * periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k := by
  simp_rw [gradientTensor_component hs]
  exact periodicFourierCoeff_component_derivative hp hs i j k

 theorem periodicFourierCoeff_vector_laplacian {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ ∞ v) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ (NSFormalization.Section3.T12.laplacian v x i : ℂ)) k =
      (-periodicAngularFrequencySq k : ℂ) * periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k := by
  have hd (j : Fin 3) : ContDiff ℝ ∞ (NSFormalization.Section4.A05.dirDeriv j v) :=
    (hs.fderiv_right (by simp)).clm_apply contDiff_const
  have hfirst (j : Fin 3) :
      (fun x ↦ (NSFormalization.Section4.A05.dirDeriv j v x i : ℂ)) =
        spatialPartial j (fun x ↦ (v x i : ℂ)) := by
    funext x
    exact gradientTensor_component (hs.of_le (by simp)) i j x
  have hsecond (j : Fin 3) (x : Space) :
      (NSFormalization.Section4.A05.dirDeriv j (NSFormalization.Section4.A05.dirDeriv j v) x i : ℂ) =
        spatialPartial j (spatialPartial j (fun y ↦ (v y i : ℂ))) x := by
    rw [← hfirst]
    exact gradientTensor_component ((hd j).of_le (by simp)) i j x
  have he : (fun x ↦ (NSFormalization.Section3.T12.laplacian v x i : ℂ)) =
      fun x ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j (fun y ↦ (v y i : ℂ))) x := by
    funext x
    simp only [NSFormalization.Section3.T12.laplacian, NSFormalization.Section4.A05.lap,
      WithLp.ofLp_sum, Finset.sum_apply, Complex.ofReal_sum, hsecond]
  rw [he]
  exact periodicFourierCoeff_component_laplacian hp (hs.of_le (by simp)) i k

end NSFormalization.Section3.T10
