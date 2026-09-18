import NSFormalization.Section3.T11.LocalTheory
import NSFormalization.Section3.T10.PhysicalBridge
import NSFormalization.Paper1.FourierReconstructionAdapter
import NSFormalization.Paper1.PeriodicPressureNormalization
import NavierStokes.R3.ConservativeDifference

/-!
# Galilean class and translation algebra

This module proves the three algebraic/class-preservation fields assigned to
T11/U3.  The physical translation lemmas are stated for arbitrary integrable
periodic fields, so the Sobolev result also covers the empty-datum (`⊤`) case.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration
open NavierStokes.PeriodicUniqueness
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar IsSolenoidal)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators ComplexConjugate

/-- The explicit product Haar measure used by T10 is translation invariant. -/
instance galileanPeriodicTorusMeasure_isAddRightInvariant :
    periodicTorusMeasure.IsAddRightInvariant := by
  change (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle).IsAddRightInvariant
  infer_instance

private def torusPoint (y : Space) : PeriodicTorus :=
  fun i => (y i : UnitAddCircle)

private lemma isPeriodicSpatial_translate {E : Type*} [AddCommMonoid E]
    {z : Space → E} (hz : IsPeriodicSpatial z) (y : Space) :
    IsPeriodicSpatial (fun x => z (x + y)) := by
  intro x i
  change z ((x + coordinateVector i) + y) = z (x + y)
  rw [show (x + coordinateVector i) + y =
      (x + y) + coordinateVector i by abel]
  exact hz (x + y) i

private lemma torusLift_translate {E : Type*} [AddCommMonoid E]
    {z : Space → E} (hz : IsPeriodicSpatial z) (y : Space) (q : PeriodicTorus) :
    torusLift (fun x => z (x + y)) q = torusLift z (q + torusPoint y) := by
  let x : Space := toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) q).val)
  have hqx : (fun i ↦ (x i : UnitAddCircle)) = q := by
    exact (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).symm_apply_apply q
  rw [show torusLift (fun x => z (x + y)) q = z (x + y) by
    unfold torusLift NSFormalization.Paper1.torusLift
    rfl]
  rw [← torusLift_apply_of_periodic hz (x + y)]
  congr 1
  ext i
  simp only [Pi.add_apply, torusPoint]
  rw [← hqx]
  rfl

private lemma integrable_torusLift_translate_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : Space → E} (hz : IsPeriodicSpatial z) (y : Space) :
    Integrable (torusLift (fun x ↦ z (x + y))) periodicTorusMeasure ↔
      Integrable (torusLift z) periodicTorusMeasure := by
  rw [show torusLift (fun x ↦ z (x + y)) =
      fun q ↦ torusLift z (q + torusPoint y) from
    funext (torusLift_translate hz y)]
  constructor
  · intro h
    have hb := MeasurePreserving.integrable_comp_of_integrable
      (measurePreserving_add_right periodicTorusMeasure (-torusPoint y)) h
    have heq : ((fun q ↦ torusLift z (q + torusPoint y)) ∘
        fun q ↦ q + -torusPoint y) = torusLift z := by
      funext q
      change torusLift z ((q + -torusPoint y) + torusPoint y) = torusLift z q
      rw [add_assoc, neg_add_cancel, add_zero]
    rw [heq] at hb
    exact hb
  · intro h
    exact MeasurePreserving.integrable_comp_of_integrable
      (g := torusLift z)
      (measurePreserving_add_right periodicTorusMeasure (torusPoint y)) h

private lemma meanT_translate {z : SpatialField}
    (hz : IsPeriodicSpatial z) (y : Space) :
    meanT (fun x ↦ z (x + y)) = meanT z := by
  unfold meanT
  simp_rw [torusLift_translate hz y]
  exact integral_add_right_eq_self (μ := periodicTorusMeasure)
    (torusLift z) (torusPoint y)

private lemma periodicFourierCoeff_translate {z : Space → ℂ}
    (hz : IsPeriodicSpatial z) (y : Space) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ z (x + y)) k =
      UnitAddTorus.mFourier k (torusPoint y) * periodicFourierCoeff z k := by
  unfold periodicFourierCoeff NSFormalization.Paper1.periodicFourierCoeff
  unfold UnitAddTorus.mFourierCoeff
  simp_rw [torusLift_translate hz y]
  have hshift := integral_add_right_eq_self (μ := periodicTorusMeasure)
    (fun q : PeriodicTorus ↦
      UnitAddTorus.mFourier (-k) (q - torusPoint y) • torusLift z q)
    (torusPoint y)
  simp only [add_sub_cancel_right] at hshift
  rw [hshift]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  change UnitAddTorus.mFourier (-k) (q - torusPoint y) * torusLift z q =
    UnitAddTorus.mFourier k (torusPoint y) *
      (UnitAddTorus.mFourier (-k) q * torusLift z q)
  rw [show UnitAddTorus.mFourier (-k) (q - torusPoint y) =
      UnitAddTorus.mFourier (-k) q * UnitAddTorus.mFourier k (torusPoint y) by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, Pi.sub_apply]
    rw [show (∏ i, fourier (-k i) (q i - torusPoint y i)) =
        ∏ i, (fourier (-k i) (q i) * fourier (-k i) (-torusPoint y i)) by
      apply Finset.prod_congr rfl
      intro i _
      rw [show q i - torusPoint y i = q i + -torusPoint y i by abel]
      simp only [fourier_apply]
      rw [zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]]
    rw [Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp [fourier_apply]]
  ring

private def translateScalarData (y : Space) (A : PeriodicScalarData) :
    PeriodicScalarData :=
  ⟨fun k ↦ UnitAddTorus.mFourier k (torusPoint y) * A k, by
    apply memℓp_gen
    have hA := (lp.memℓp A).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, norm_mul, Real.rpow_two,
      show ∀ k : PeriodicFrequency,
          ‖UnitAddTorus.mFourier k (torusPoint y)‖ = 1 by
        intro k
        simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
          fourier_apply, Circle.norm_coe, Finset.prod_const_one], one_mul] using hA⟩

private lemma translateScalarData_norm (y : Space) (A : PeriodicScalarData) :
    ‖translateScalarData y A‖ = ‖A‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  apply tsum_congr
  intro k
  simp only [translateScalarData, norm_mul, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
    Finset.prod_const_one, one_mul]

private def translatePeriodicDatum (s : ℝ) (y : Space) (A : PeriodicSobolev s) :
    PeriodicSobolev s := by
  let B : PeriodicVectorData := WithLp.toLp 2 (fun i ↦ translateScalarData y (A.1 i))
  refine ⟨B, ?_⟩
  intro i k
  change UnitAddTorus.mFourier (-k) (torusPoint y) * A.1 i (-k) =
    star (UnitAddTorus.mFourier k (torusPoint y) * A.1 i k)
  rw [A.2 i k, UnitAddTorus.mFourier_neg]
  exact (map_mul (starRingEnd ℂ)
    (UnitAddTorus.mFourier k (torusPoint y)) (A.1 i k)).symm

private lemma translatePeriodicDatum_norm (s : ℝ) (y : Space)
    (A : PeriodicSobolev s) : ‖translatePeriodicDatum s y A‖ = ‖A‖ := by
  change ‖(translatePeriodicDatum s y A).1‖ = ‖A.1‖
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (translatePeriodicDatum s y A).1 i = translateScalarData y (A.1 i) by
      simp only [translatePeriodicDatum, PiLp.toLp_apply],
    translateScalarData_norm]

private lemma isPeriodicDatum_translate {s : ℝ} {z : SpatialField}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s z A) (y : Space) :
    IsPeriodicDatum s (fun x ↦ z (x + y)) (translatePeriodicDatum s y A) := by
  refine ⟨isPeriodicSpatial_translate hA.1 y,
    (integrable_torusLift_translate_iff hA.1 y).2 hA.2.1, ?_⟩
  intro i k
  simp only [translatePeriodicDatum, PiLp.toLp_apply, translateScalarData]
  change UnitAddTorus.mFourier k (torusPoint y) * A.1 i k =
    (periodicFrequencyWeight k) ^ (s / 2) •
      periodicFourierCoeff (fun x ↦ ((z (x + y) i : ℝ) : ℂ)) k
  have hcoeff :
      periodicFourierCoeff (fun x ↦ ((z (x + y) i : ℝ) : ℂ)) k =
        UnitAddTorus.mFourier k (torusPoint y) *
          periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k := by
    apply periodicFourierCoeff_translate
      (z := fun x ↦ ((z x i : ℝ) : ℂ))
    intro x j
    exact congrArg (fun v : Space ↦ ((v i : ℝ) : ℂ)) (hA.1 x j)
  rw [hA.2.2 i k, hcoeff]
  exact mul_smul_comm _ _ _

private lemma periodicSobolevENorm_translate_le (s : ℝ) {z : SpatialField}
    (_hz : IsPeriodicSpatial z) (y : Space) :
    periodicSobolevENorm s (fun x ↦ z (x + y)) ≤ periodicSobolevENorm s z := by
  unfold periodicSobolevENorm
  apply le_iInf
  intro A
  refine (iInf_le_of_le
    (⟨translatePeriodicDatum s y A.1, isPeriodicDatum_translate A.2 y⟩ :
      {B : PeriodicSobolev s // IsPeriodicDatum s (fun x ↦ z (x + y)) B}) ?_)
  simpa only [← ofReal_norm, translatePeriodicDatum_norm] using
    (le_rfl : ENNReal.ofReal ‖A.1‖ ≤ ENNReal.ofReal ‖A.1‖)

/-- Spatial translation preserves the extended periodic Sobolev norm at every
real order, including when the datum type is empty and the norm is `⊤`. -/
theorem translation_preserves_sobolev : ∀ (s : ℝ) (z : SpatialField),
    IsPeriodicSpatial z → ∀ y : Space,
      periodicSobolevENorm s (fun x ↦ z (x + y)) =
        periodicSobolevENorm s z := by
  intro s z hz y
  apply le_antisymm (periodicSobolevENorm_translate_le s hz y)
  have h := periodicSobolevENorm_translate_le s
    (isPeriodicSpatial_translate hz y) (-y)
  have heq : (fun x ↦ z ((x + -y) + y)) = z := by
    funext x
    rw [add_assoc, neg_add_cancel, add_zero]
  simpa only [heq] using h

/-! ## Smooth means and the transformed data classes -/

/-- Global smoothness passes through the scalar cube integral.  The existing
half-open-interval theorem is applied after translating an arbitrary time to
the interior point `1 ∈ [0,2)`. -/
private lemma cubeIntegral_contDiff_of_contDiff {F : SpaceTime → ℝ}
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun t ↦ cubeIntegral (fun x ↦ F (t, x))) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  let G : SpaceTime → ℝ := fun z ↦ F (z.1 + (t - 1), z.2)
  have hG : ContDiff ℝ ∞ G :=
    hF.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  have hm : ContDiffOn ℝ ∞ (fun r ↦ cubeIntegral (fun x ↦ G (r, x)))
      (Ico (0 : ℝ) 2) :=
    NSFormalization.Paper1.PeriodicPressureNormalization.pressureMean_contDiffOn
      hG.contDiffOn
  have hm1 : ContDiffAt ℝ ∞ (fun r ↦ cubeIntegral (fun x ↦ G (r, x))) 1 :=
    hm.contDiffAt (Ico_mem_nhds zero_lt_one one_lt_two)
  let e : ℝ → ℝ := fun r ↦ r - t + 1
  have he : ContDiff ℝ ∞ e := (contDiff_id.sub contDiff_const).add contDiff_const
  have het : e t = 1 := by dsimp [e]; ring
  have hm_et : ContDiffAt ℝ ∞
      (fun r ↦ cubeIntegral (fun x ↦ G (r, x))) (e t) := by
    rw [het]
    exact hm1
  have hc := hm_et.comp t he.contDiffAt
  have heq :
      ((fun r ↦ cubeIntegral (fun x ↦ G (r, x))) ∘ e) =
        (fun r ↦ cubeIntegral (fun x ↦ F (r, x))) := by
    funext r
    change cubeIntegral (fun x ↦ G (e r, x)) =
      cubeIntegral (fun x ↦ F (r, x))
    congr 1
    funext x
    dsimp [G, e]
    congr 2
    ring
  rw [heq] at hc
  exact hc

private lemma forceMeanT_contDiff {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (forceMeanT f) := by
  have hmean : forceMeanT f = fun t ↦ cubeIntegral (fun x ↦ f (t, x)) := by
    funext t
    exact NSFormalization.Paper1.integral_torusLift (fun x ↦ f (t, x))
  rw [hmean]
  apply (contDiff_piLp 2).mpr
  intro i
  have hi : ContDiff ℝ ∞ (fun z : SpaceTime ↦ (f z) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hci := cubeIntegral_contDiff_of_contDiff hi
  convert hci using 1
  funext t
  simp only [cubeIntegral]
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (integrable_cube
      (hf.continuous.comp (continuous_const.prodMk continuous_id)))).symm

private lemma intervalPrimitive_contDiff {g : ℝ → Space}
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun t ↦ ∫ r in (0 : ℝ)..t, g r) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · intro t
    exact (intervalIntegral.integral_hasDerivAt_right
      (hg.continuous.intervalIntegrable 0 t)
      hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuous.continuousAt).differentiableAt
  · have hd : deriv (fun t ↦ ∫ r in (0 : ℝ)..t, g r) = g := by
      funext t
      exact (intervalIntegral.integral_hasDerivAt_right
        (hg.continuous.intervalIntegrable 0 t)
        hg.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hg.continuous.continuousAt).deriv
    rw [hd]
    exact hg

private lemma galileanMeanT_contDiff {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (galileanMeanT a f) := by
  exact contDiff_const.add (intervalPrimitive_contDiff (forceMeanT_contDiff hf))

private lemma galileanShiftT_contDiff {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (galileanShiftT a f) := by
  exact intervalPrimitive_contDiff (galileanMeanT_contDiff hf)

private lemma meanZeroPartT_solenoidal {a : SpatialField}
    (ha : ContDiff ℝ ∞ a) (hdiv : IsSolenoidal a) :
    IsSolenoidal (meanZeroPartT a) := by
  intro x
  have hconst : ContDiff ℝ ∞ (fun _ : Space ↦ meanT a) := contDiff_const
  change spatialDivergence
      (fun z : SpaceTime ↦ a z.2 - meanT a) 0 x = 0
  rw [show (fun z : SpaceTime ↦ a z.2 - meanT a) =
      (fun z : SpaceTime ↦ a z.2) - (fun _ : SpaceTime ↦ meanT a) by rfl,
    spatialDivergence_sub ha hconst x, hdiv x]
  simp [spatialDivergence, spatialDerivative]

/-- Centering the datum and applying the data-defined Galilean translation
preserve the two canonical smooth periodic input classes. -/
theorem transformed_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (_w : ClassicalSolutionT ν a f T),
          meanZeroPartT a ∈ initialClassT ∧
            galileanForceT a f ∈ forceClassT := by
  intro _ν _hν a ha f hf _T _w
  rcases ha with ⟨ha_smooth, ha_periodic, ha_div⟩
  rcases hf with ⟨hf_smooth, hf_periodic, K, hK_compact, hK_pos, hf_support⟩
  have hfm := forceMeanT_contDiff hf_smooth
  have hshift := galileanShiftT_contDiff (a := a) hf_smooth
  constructor
  · refine ⟨ha_smooth.sub contDiff_const, ?_,
      meanZeroPartT_solenoidal ha_smooth ha_div⟩
    intro x i
    simp only [meanZeroPartT]
    rw [ha_periodic x i]
  · refine ⟨?_, ?_, K, hK_compact, hK_pos, ?_⟩
    · exact (hf_smooth.comp
        (contDiff_fst.prodMk
          (contDiff_snd.add (hshift.comp contDiff_fst)))).sub
        (hfm.comp contDiff_fst)
    · intro t _ht x i
      simp only [galileanForceT]
      rw [show x + coordinateVector i + galileanShiftT a f t =
          (x + galileanShiftT a f t) + coordinateVector i by abel,
        hf_periodic t (mem_univ t) (x + galileanShiftT a f t) i]
    · apply closure_minimal _ (hK_compact.isClosed.prod isClosed_univ)
      intro z hz
      refine ⟨?_, mem_univ z.2⟩
      by_contra hzt
      have hf_zero (x : Space) : f (z.1, x) = 0 := by
        by_contra hn
        have hs : (z.1, x) ∈ tsupport f := subset_tsupport f hn
        exact hzt (hf_support hs).1
      have hmean_zero : forceMeanT f z.1 = 0 := by
        simp [forceMeanT, meanT, hf_zero,
          torusLift, NSFormalization.Paper1.torusLift]
      exact hz (by simp [galileanForceT, hf_zero, hmean_zero])

/-! ## Evolution and cancellation of the spatial mean -/

private lemma cubeIntegral_apply {g : Space → Space} (hg : Continuous g)
    (i : Fin 3) : (cubeIntegral g) i = cubeIntegral (fun x ↦ g x i) := by
  unfold cubeIntegral
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (integrable_cube hg)).symm

private lemma cubeIntegral_laplacian_component_eq_zero {u : SpaceTimeField}
    {t : ℝ} (hu : ContDiff ℝ ∞ (fun x ↦ u (t, x)))
    (hp : IsPeriodicSpatial (fun x ↦ u (t, x))) (k : Fin 3) :
    cubeIntegral (fun x ↦ spatialLaplacian u t x k) = 0 := by
  rw [show (fun x ↦ spatialLaplacian u t x k) =
      NavierStokesR3.ConservativeDifference.scalarLaplacian
        (fun x ↦ u (t, x) k) by
    funext x
    exact NavierStokesR3.ConservativeDifference.spatialLaplacian_component hu x k]
  unfold NavierStokesR3.ConservativeDifference.scalarLaplacian
  calc
    cubeIntegral (fun x ↦ ∑ i : Fin 3,
        spatialPartial i (spatialPartial i (fun y ↦ u (t, y) k)) x) =
        ∑ i : Fin 3, cubeIntegral
          (spatialPartial i (spatialPartial i (fun y ↦ u (t, y) k))) := by
      exact cubeIntegral_sum Finset.univ _ (fun i _ ↦
        (spatial_partial_contDiff
          (spatial_partial_contDiff (component_contDiff hu k) i) i).continuous)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      exact cubeIntegral_partial_eq_zero
        ((spatial_partial_contDiff (component_contDiff hu k) i).of_le (by simp))
        (spatial_partial_periodic
          (component_periodic (show UnitPeriods (fun x ↦ u (t, x)) from hp) k) i) i

private lemma cubeIntegral_pressure_component_eq_zero {p : SpaceTimeScalar}
    {t : ℝ} (hp_smooth : ContDiff ℝ ∞ (fun x ↦ p (t, x)))
    (hp_periodic : IsPeriodicSpatial (fun x ↦ p (t, x))) (k : Fin 3) :
    cubeIntegral (fun x ↦ pressureGradient p t x k) = 0 := by
  rw [show (fun x ↦ pressureGradient p t x k) =
      spatialPartial k (fun x ↦ p (t, x)) by
    funext x
    exact NavierStokesR3.ConservativeDifference.pressureGradient_component p t x k]
  exact cubeIntegral_partial_eq_zero (hp_smooth.of_le (by simp)) hp_periodic k

private lemma cubeIntegral_advection_component_eq_zero {u : SpaceTimeField}
    {t : ℝ} (hu : ContDiff ℝ ∞ (fun x ↦ u (t, x)))
    (hp : IsPeriodicSpatial (fun x ↦ u (t, x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0) (k : Fin 3) :
    cubeIntegral (fun x ↦ advection u t x k) = 0 := by
  have heq : (fun x ↦ advection u t x k) = fun x ↦
      ∑ i : Fin 3, spatialPartial i
        (fun y ↦ u (t, y) k * u (t, y) i) x := by
    funext x
    have h := NavierStokesR3.ConservativeDifference.outerProduct_divergence hu x k
    rw [hdiv x, mul_zero, zero_add] at h
    exact h.symm
  rw [heq]
  calc
    cubeIntegral (fun x ↦ ∑ i : Fin 3, spatialPartial i
        (fun y ↦ u (t, y) k * u (t, y) i) x) =
        ∑ i : Fin 3, cubeIntegral
          (spatialPartial i (fun y ↦ u (t, y) k * u (t, y) i)) := by
      exact cubeIntegral_sum Finset.univ _ (fun i _ ↦
        (spatial_partial_contDiff
          ((component_contDiff hu k).mul (component_contDiff hu i)) i).continuous)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      apply cubeIntegral_partial_eq_zero
        (((component_contDiff hu k).mul (component_contDiff hu i)).of_le (by simp))
      intro x j
      change u (t, x + coordinateVector j) k *
          u (t, x + coordinateVector j) i = u (t, x) k * u (t, x) i
      have hper : u (t, x + coordinateVector j) = u (t, x) := hp x j
      rw [hper]

private lemma velocityMean_hasDerivAt {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {T t : ℝ} (hf : ContDiff ℝ ∞ f)
    (w : ClassicalSolutionT ν a f T) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t := by
  have hv_open : ContDiffOn ℝ ∞ w.velocity
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    w.velocity_smooth.mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hv_one : ContDiffOn ℝ 1 w.velocity
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) := hv_open.of_le (by simp)
  have hd := hasDerivAt_cubeIntegral_of_contDiffOn isOpen_Ioo hv_one ht
  have hmean : velocityMeanT w.velocity =
      fun s ↦ cubeIntegral (fun x ↦ w.velocity (s, x)) := by
    funext s
    exact NSFormalization.Paper1.integral_torusLift
      (fun x ↦ w.velocity (s, x))
  rw [hmean]
  apply hd.congr_deriv
  have hu : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) :=
    w.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨⟨ht.1.le, ht.2⟩, mem_univ x⟩)
  have hp_smooth : ContDiff ℝ ∞ (fun x ↦ w.pressure (t, x)) :=
    w.pressure_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨⟨ht.1.le, ht.2⟩, mem_univ x⟩)
  have htime_on := NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative
    (isOpen_Ioo.prod isOpen_univ) hv_open
  have htime : ContDiff ℝ ∞
      (fun x ↦ temporalDerivative w.velocity t x) :=
    htime_on.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨ht, mem_univ x⟩)
  have hf_slice : ContDiff ℝ ∞ (fun x ↦ f (t, x)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hadv : ContDiff ℝ ∞ (fun x ↦ advection w.velocity t x) :=
    (NavierStokes.ResidualRegularity.contDiffOn_advection
      (isOpen_Ioo.prod isOpen_univ) hv_open).comp_contDiff
        (contDiff_const.prodMk contDiff_id) (fun x ↦ ⟨ht, mem_univ x⟩)
  have hlap : ContDiff ℝ ∞ (fun x ↦ spatialLaplacian w.velocity t x) :=
    spatialLaplacian_contDiff hu
  have hpgrad : ContDiff ℝ ∞ (fun x ↦ pressureGradient w.pressure t x) :=
    pressureGradient_contDiff hp_smooth
  have hforce_cube : forceMeanT f t = cubeIntegral (fun x ↦ f (t, x)) :=
    NSFormalization.Paper1.integral_torusLift (fun x ↦ f (t, x))
  rw [hforce_cube]
  ext k
  change (cubeIntegral (fun x ↦ temporalDerivative w.velocity t x)) k =
    (cubeIntegral (fun x ↦ f (t, x))) k
  rw [cubeIntegral_apply htime.continuous k,
    cubeIntegral_apply hf_slice.continuous k]
  have hfield : (fun x ↦ temporalDerivative w.velocity t x k) =
      (fun x ↦ f (t, x) k - advection w.velocity t x k +
        ν * spatialLaplacian w.velocity t x k -
          pressureGradient w.pressure t x k) := by
    funext x
    have hm := congrArg (fun v : Space ↦ v k) (w.momentum t ht x)
    change temporalDerivative w.velocity t x k + advection w.velocity t x k -
        ν * spatialLaplacian w.velocity t x k +
          pressureGradient w.pressure t x k = f (t, x) k at hm
    linarith
  rw [hfield,
    cubeIntegral_sub
      (((component_contDiff hf_slice k).sub (component_contDiff hadv k)).add
        (contDiff_const.mul (component_contDiff hlap k))).continuous
      (component_contDiff hpgrad k).continuous,
    cubeIntegral_add
      ((component_contDiff hf_slice k).sub (component_contDiff hadv k)).continuous
      (contDiff_const.mul (component_contDiff hlap k)).continuous,
    cubeIntegral_sub (component_contDiff hf_slice k).continuous
      (component_contDiff hadv k).continuous,
    cubeIntegral_const_mul,
    cubeIntegral_advection_component_eq_zero hu
      (w.velocity_periodic t ⟨ht.1.le, ht.2⟩)
      (w.divergence t ⟨ht.1.le, ht.2⟩) k,
    cubeIntegral_laplacian_component_eq_zero hu
      (w.velocity_periodic t ⟨ht.1.le, ht.2⟩) k,
    cubeIntegral_pressure_component_eq_zero hp_smooth
      (w.pressure_periodic t ⟨ht.1.le, ht.2⟩) k]
  ring

private lemma velocityMean_eq_galileanMean {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {T : ℝ} (hf : ContDiff ℝ ∞ f)
    (w : ClassicalSolutionT ν a f T) :
    ∀ t ∈ Ico (0 : ℝ) T,
      velocityMeanT w.velocity t = galileanMeanT a f t := by
  intro t ht
  have hzero : velocityMeanT w.velocity 0 = meanT a := by
    unfold velocityMeanT
    congr 1
    funext x
    exact w.initial x
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · simp [galileanMeanT, hzero]
  · have hmean : velocityMeanT w.velocity =
        fun s ↦ cubeIntegral (fun x ↦ w.velocity (s, x)) := by
      funext s
      exact NSFormalization.Paper1.integral_torusLift
        (fun x ↦ w.velocity (s, x))
    have hcont : ContinuousOn (velocityMeanT w.velocity) (Icc (0 : ℝ) t) := by
      rw [hmean]
      apply cubeIntegral_continuousOn_Icc
      exact w.velocity_smooth.continuousOn.mono (fun z hz ↦
        ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩)
    have hfm := forceMeanT_contDiff hf
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht_pos.le
      hcont (fun r hr ↦ velocityMean_hasDerivAt hf w
        ⟨hr.1, hr.2.trans ht.2⟩)
      (hfm.continuous.intervalIntegrable 0 t)
    unfold galileanMeanT
    rw [← hzero, hftc]
    abel

private lemma meanT_sub_const {z : SpatialField} (hz : Integrable (torusLift z)
    periodicTorusMeasure) (c : Space) :
    meanT (fun x ↦ z x - c) = meanT z - c := by
  change (∫ y : PeriodicTorus, torusLift z y - c ∂periodicTorusMeasure) =
    meanT z - c
  rw [integral_sub hz (integrable_const c)]
  change meanT z - meanT (fun _ : Space ↦ c) = meanT z - c
  rw [meanT_const]

private lemma integrable_torusLift_of_contDiff_periodic {z : SpatialField}
    (hz_smooth : ContDiff ℝ ∞ z) (hz_periodic : IsPeriodicSpatial z) :
    Integrable (torusLift z) periodicTorusMeasure := by
  apply Integrable.of_eval_piLp
  intro i
  have hc : Continuous (fun x ↦ ((z x i : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hz_smooth)).continuous
  have hp : IsPeriodicSpatial (fun x ↦ ((z x i : ℝ) : ℂ)) :=
    fun x j ↦ congrArg (fun v : Space ↦ ((v i : ℝ) : ℂ)) (hz_periodic x j)
  have hi : Integrable (torusLift (fun x ↦ ((z x i : ℝ) : ℂ)))
      periodicTorusMeasure := by
    simpa using (NSFormalization.Paper1.continuous_torusLift hc hp).continuousOn
      |>.integrableOn_compact (μ := periodicTorusMeasure) isCompact_univ
  exact hi.re

/-- The centered datum, translated velocity, and translated force all have
zero normalized spatial mean on the canonical solution interval. -/
theorem transformed_mean_zero : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          meanT (meanZeroPartT a) = 0 ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanVelocityT a f w.velocity (t, x)) = 0) ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanForceT a f (t, x)) = 0) := by
  intro _ν _hν a ha f hf T w
  rcases ha with ⟨ha_smooth, ha_periodic, _ha_div⟩
  rcases hf with ⟨hf_smooth, hf_periodic, _K, _hK_compact, _hK_pos, _hf_support⟩
  have ha_int := integrable_torusLift_of_contDiff_periodic ha_smooth ha_periodic
  refine ⟨(mean_decomposition a ha_periodic ha_int).2, ?_, ?_⟩
  · intro t ht
    obtain ⟨Gu, _hGu, hGuDatum⟩ := w.sobolev 0
    have huDatum := hGuDatum t ht
    have hu_periodic : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) :=
      w.velocity_periodic t ht
    have hu_trans_int : Integrable
        (torusLift (fun x ↦ w.velocity
          (t, x + galileanShiftT a f t))) periodicTorusMeasure :=
      (integrable_torusLift_translate_iff hu_periodic
        (galileanShiftT a f t)).2 huDatum.2.1
    change meanT (fun x ↦ w.velocity
      (t, x + galileanShiftT a f t) - galileanMeanT a f t) = 0
    rw [meanT_sub_const hu_trans_int,
      meanT_translate hu_periodic (galileanShiftT a f t),
      show meanT (fun x ↦ w.velocity (t, x)) =
          velocityMeanT w.velocity t by rfl,
      velocityMean_eq_galileanMean hf_smooth w t ht, sub_self]
  · intro t _ht
    have hf_slice_smooth : ContDiff ℝ ∞ (fun x ↦ f (t, x)) :=
      hf_smooth.comp (contDiff_const.prodMk contDiff_id)
    have hf_slice_periodic : IsPeriodicSpatial (fun x ↦ f (t, x)) :=
      hf_periodic t (mem_univ t)
    have hf_trans_int : Integrable
        (torusLift (fun x ↦ f (t, x + galileanShiftT a f t)))
          periodicTorusMeasure :=
      (integrable_torusLift_translate_iff hf_slice_periodic
        (galileanShiftT a f t)).2
          (integrable_torusLift_of_contDiff_periodic
            hf_slice_smooth hf_slice_periodic)
    change meanT (fun x ↦ f (t, x + galileanShiftT a f t) -
      forceMeanT f t) = 0
    rw [meanT_sub_const hf_trans_int,
      meanT_translate hf_slice_periodic (galileanShiftT a f t),
      show meanT (fun x ↦ f (t, x)) = forceMeanT f t by rfl, sub_self]

end NSFormalization.Section3.T11
