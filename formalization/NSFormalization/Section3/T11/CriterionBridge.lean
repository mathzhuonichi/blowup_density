import NSFormalization.Section3.T11.FlowConversion
import NSFormalization.Section3.T10.FourierCalculus
import NSFormalization.Paper1.PeriodicFiniteH2Bridge

/-! All-order datum existence and the squared H² continuation criterion. -/
noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicLocalLifespan
open scoped ContDiff ENNReal BigOperators

/-- Uniqueness evaluates the infimum at any representing datum. -/
theorem periodicSobolevENorm_eq_datum {s : ℝ} {z : SpatialField}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s z A) :
    periodicSobolevENorm s z = ‖A‖ₑ := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨A, hA⟩ le_rfl
  · apply le_iInf
    intro B
    rw [datum_unique s z B.1 A B.2 hA]

/-- Smooth periodic vector fields have data at every real order. -/
theorem exists_periodicDatum_smooth (s : ℝ) {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    ∃ A : PeriodicSobolev s, IsPeriodicDatum s z A := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun x ↦ (z x i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)
  have hpc (i : Fin 3) : IsPeriodicSpatial (fun x ↦ (z x i : ℂ)) :=
    fun x j ↦ by dsimp; rw [hp x j]
  let a : PeriodicVectorData := WithLp.toLp 2 (fun i ↦
    NSFormalization.Paper1.smoothPeriodicWeightedFourierLp s _ (hc i) (hpc i))
  have ha (i : Fin 3) (k : PeriodicFrequency) : a i k =
      periodicFrequencyWeight k ^ (s / 2) •
        periodicFourierCoeff (fun x ↦ (z x i : ℂ)) k := by
    change NSFormalization.Paper1.periodicFrequencyWeight k ^ (s / 2) • _ = _
    rw [periodicFrequencyWeight_eq_paper1]
  have hr : a ∈ realPeriodicSubmodule := by
    intro i k
    rw [ha, ha, periodicFourierCoeff_real_neg]
    have hw : periodicFrequencyWeight (-k) = periodicFrequencyWeight k := by
      simp [periodicFrequencyWeight]
    rw [hw]
    simp
  refine ⟨⟨a, hr⟩, hp, ?_, ha⟩
  apply Integrable.of_eval_piLp
  intro i
  have hi : Integrable (torusLift (fun x ↦ (z x i : ℂ))) periodicTorusMeasure := by
    simpa using (NSFormalization.Paper1.continuous_torusLift (hc i).continuous
      (hpc i)).continuousOn.integrableOn_compact (μ := periodicTorusMeasure) isCompact_univ
  exact hi.re

/-- In particular the total extended norm is finite. -/
theorem periodicSobolevENorm_ne_top_smooth (s : ℝ) {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    periodicSobolevENorm s z ≠ ⊤ := by
  obtain ⟨A, hA⟩ := exists_periodicDatum_smooth s hs hp
  rw [periodicSobolevENorm_eq_datum hA]
  exact enorm_ne_top

/-- The datum norm is exactly the scalar-component Bessel norm of Paper 1. -/
theorem norm_periodicDatum {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    ‖A‖ = periodicVectorSobolevNorm s u t := by
  change ‖A.1‖ = _
  rw [PiLp.norm_eq_of_L2]
  unfold periodicVectorSobolevNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (tsum_nonneg (fun _ ↦ sq_nonneg _))]
  unfold NSFormalization.Paper1.periodicSobolevSq
  apply tsum_congr
  intro k
  rw [hA.2.2, periodicFrequencyWeight_eq_paper1]
  exact NSFormalization.Paper1.norm_periodicWeightedCoeff_sq s _ k

/-- Identification of the extended norm whenever a datum exists. -/
theorem periodicSobolevENorm_eq_of_datum {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    periodicSobolevENorm s (fun x ↦ u (t, x)) =
      ENNReal.ofReal (periodicVectorSobolevNorm s u t) := by
  rw [periodicSobolevENorm_eq_datum hA, ← ofReal_norm, norm_periodicDatum hA]

/-- Smooth periodic slices satisfy the same norm identification at every real order. -/
theorem periodicSobolevENorm_eq_smooth (s : ℝ) (u : SpaceTimeField) (t : ℝ)
    (hs : ContDiff ℝ ∞ (fun x ↦ u (t, x)))
    (hp : IsPeriodicSpatial (fun x ↦ u (t, x))) :
    periodicSobolevENorm s (fun x ↦ u (t, x)) =
      ENNReal.ofReal (periodicVectorSobolevNorm s u t) := by
  obtain ⟨A, hA⟩ := exists_periodicDatum_smooth s hs hp
  exact periodicSobolevENorm_eq_of_datum hA

/-- Continuity holds on the solution interval, where the velocity is constrained. -/
theorem continuousOn_periodicSobolevENorm {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (m : ℕ) :
    ContinuousOn (fun t ↦ periodicSobolevENorm (m : ℝ) (fun x ↦ w.velocity (t, x)))
      (Ico (0 : ℝ) T) := by
  obtain ⟨G, hG, hd⟩ := w.sobolev m
  apply (ENNReal.continuous_ofReal.comp_continuousOn hG.norm).congr
  intro t ht
  exact (periodicSobolevENorm_eq_datum (hd t ht)).trans (ofReal_norm _).symm

/-- In particular the H² norm is measurable for the restricted time measure. -/
theorem aemeasurable_periodicSobolevENorm {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) :
    AEMeasurable (fun t ↦ periodicSobolevENorm 2 (fun x ↦ w.velocity (t, x)))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  exact ((continuousOn_periodicSobolevENorm w 2).mono Ioo_subset_Ico_self).aemeasurable
    measurableSet_Ioo

/-- The real squared profile is continuous before the terminal endpoint. -/
theorem continuousOn_h2SquaredProfile {ν S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f S) :
    ContinuousOn (h2SquaredProfile (toFlow w)) (Ico (0 : ℝ) S) := by
  obtain ⟨G, hG, hd⟩ := w.sobolev 2
  apply (hG.norm.pow 2).congr
  intro t ht
  exact congrArg (fun r : ℝ ↦ r ^ 2) (norm_periodicDatum (hd t ht)).symm

/-- Both versions of the squared H² criterion are equivalent, including
measurability. Changing the single terminal endpoint has no measure effect. -/
theorem squaredHTwoIntegralT_ne_top_iff_finiteH2Energy
    {ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f S) :
    squaredHTwoIntegralT S w.velocity ≠ ⊤ ↔ FiniteH2Energy (toFlow w) := by
  have he : squaredHTwoIntegralT S w.velocity =
      ∫⁻ t in Ioo (0 : ℝ) S, ENNReal.ofReal (h2SquaredProfile (toFlow w) t) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    obtain ⟨G, _, hd⟩ := w.sobolev 2
    have htD : IsPeriodicDatum 2 (fun x ↦ w.velocity (t, x)) (G t) :=
      hd t ⟨ht.1.le, ht.2⟩
    rw [periodicSobolevENorm_eq_of_datum htD]
    exact (ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2).symm
  have hm : AEStronglyMeasurable (h2SquaredProfile (toFlow w))
      (volume.restrict (Ioo (0 : ℝ) S)) :=
    ((continuousOn_h2SquaredProfile w).mono Ioo_subset_Ico_self).aestronglyMeasurable
      measurableSet_Ioo
  rw [he, FiniteH2Energy, IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc]
  rw [Integrable, and_iff_right hm, hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun t ↦
      show 0 ≤ h2SquaredProfile (toFlow w) t from sq_nonneg _)), lt_top_iff_ne_top]

/-- Non-vacuity at an arbitrary constant, including every nonzero constant. -/
example (s : ℝ) (c : Space) : periodicSobolevENorm s (fun _ ↦ c) ≠ ⊤ :=
  periodicSobolevENorm_ne_top_smooth s contDiff_const (fun _ _ ↦ rfl)

end NSFormalization.Section3.T11
