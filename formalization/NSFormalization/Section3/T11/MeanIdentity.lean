import NSFormalization.Section3.T11.GalileanClasses

/-! # Evolution of the periodic velocity mean

The public U3 cancellation theorem already contains the integrated momentum
argument. We recover the untranslated mean by Haar translation invariance,
then differentiate the prescribed primitive on the open solution interval.
The elementary adapters below mirror U3; no private names are imported.
-/

noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ContDiff

namespace MeanIdentity
lemma torusLift_translate {E : Type*} [AddCommMonoid E]
    {z : Space → E} (hz : IsPeriodicSpatial z) (y : Space) (q : PeriodicTorus) :
    torusLift (fun x => z (x + y)) q = torusLift z (q + (fun i => (y i : UnitAddCircle))) := by
  let x : Space := toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) q).val)
  have hqx : (fun i ↦ (x i : UnitAddCircle)) = q := by
    exact (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).symm_apply_apply q
  rw [show torusLift (fun x => z (x + y)) q = z (x + y) by
    unfold torusLift NSFormalization.Paper1.torusLift
    rfl]
  rw [← torusLift_apply_of_periodic hz (x + y)]
  congr 1
  ext i
  simp only [Pi.add_apply]
  rw [← hqx]
  rfl

lemma integrable_torusLift_translate_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : Space → E} (hz : IsPeriodicSpatial z) (y : Space) :
    Integrable (torusLift (fun x ↦ z (x + y))) periodicTorusMeasure ↔
      Integrable (torusLift z) periodicTorusMeasure := by
  rw [show torusLift (fun x ↦ z (x + y)) =
      fun q ↦ torusLift z (q + (fun i => (y i : UnitAddCircle))) from
    funext (torusLift_translate hz y)]
  constructor
  · intro h
    have hb := MeasurePreserving.integrable_comp_of_integrable
      (measurePreserving_add_right periodicTorusMeasure (-(fun i => (y i : UnitAddCircle)))) h
    have heq : ((fun q ↦ torusLift z (q + (fun i => (y i : UnitAddCircle)))) ∘
        fun q ↦ q + -(fun i => (y i : UnitAddCircle))) = torusLift z := by
      funext q
      change torusLift z ((q + -(fun i => (y i : UnitAddCircle))) + (fun i => (y i : UnitAddCircle))) = torusLift z q
      rw [add_assoc, neg_add_cancel, add_zero]
    rw [heq] at hb
    exact hb
  · intro h
    exact MeasurePreserving.integrable_comp_of_integrable
      (g := torusLift z)
      (measurePreserving_add_right periodicTorusMeasure ((fun i => (y i : UnitAddCircle)))) h

lemma meanT_translate {z : SpatialField}
    (hz : IsPeriodicSpatial z) (y : Space) :
    meanT (fun x ↦ z (x + y)) = meanT z := by
  unfold meanT
  simp_rw [torusLift_translate hz y]
  exact integral_add_right_eq_self (μ := periodicTorusMeasure)
    (torusLift z) ((fun i => (y i : UnitAddCircle)))

/-- Global smoothness passes through the scalar cube integral.  The existing
half-open-interval theorem is applied after translating an arbitrary time to
the interior point `1 ∈ [0,2)`. -/
lemma cubeIntegral_contDiff_of_contDiff {F : SpaceTime → ℝ}
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

lemma forceMeanT_contDiff {f : SpaceTimeField}
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

lemma meanT_sub_const {z : SpatialField} (hz : Integrable (torusLift z)
    periodicTorusMeasure) (c : Space) :
    meanT (fun x ↦ z x - c) = meanT z - c := by
  change (∫ y : PeriodicTorus, torusLift z y - c ∂periodicTorusMeasure) =
    meanT z - c
  rw [integral_sub hz (integrable_const c)]
  change meanT z - meanT (fun _ : Space ↦ c) = meanT z - c
  rw [meanT_const]

end MeanIdentity

theorem mean_formula : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            velocityMeanT w.velocity t = galileanMeanT a f t := by
  intro ν hν a ha f hf T w t ht
  have hz := (transformed_mean_zero ν hν a ha f hf T w).2.1 t ht
  obtain ⟨G, _, hG⟩ := w.sobolev 0
  have hp : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) :=
    w.velocity_periodic t ht
  have hi := (MeanIdentity.integrable_torusLift_translate_iff hp
    (galileanShiftT a f t)).2 (hG t ht).2.1
  change meanT (fun x ↦ w.velocity (t, x + galileanShiftT a f t) -
    galileanMeanT a f t) = 0 at hz
  rw [MeanIdentity.meanT_sub_const hi, MeanIdentity.meanT_translate hp] at hz
  exact sub_eq_zero.mp hz

theorem mean_derivative : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t := by
  intro ν hν a ha f hf T w t ht
  have hc := (MeanIdentity.forceMeanT_contDiff hf.1).continuous
  have hd : HasDerivAt (galileanMeanT a f) (forceMeanT f t) t := by
    exact
      (intervalIntegral.integral_hasDerivAt_right
        (hc.intervalIntegrable 0 t)
        hc.aestronglyMeasurable.stronglyMeasurableAtFilter
        hc.continuousAt).const_add (meanT a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact mean_formula ν hν a ha f hf T w r ⟨hr.1.le, hr.2⟩

end NSFormalization.Section3.T11
