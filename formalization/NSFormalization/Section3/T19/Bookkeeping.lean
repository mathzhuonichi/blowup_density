import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section3.T11.CriterionBridge
import NSFormalization.Section3.T12.SpectralGap
import NSFormalization.Section3.T15.Bridges

/-!
# T19 bookkeeping facts

The six proof units here are the arithmetic, elementary norm, and finite-energy
inputs to the periodic density package.  This implementation module is stated
only over canonical `formalization/` vocabulary; the contract-facing probe in
`research/T19/probes/bookkeeping_closes.lean` records the definitional bridges.
-/

noncomputable section

namespace NSFormalization.Section3.T19

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal Topology BigOperators

/-! ## Vocabulary required by the T19 fields -/

/-- The Section 4 threshold formula, restated on the canonical side. -/
def criticalOrder (q : ℝ) : ℝ := 2 / q - 3 / 2

/-- `03-torus.tex:129-133`: `G(t)` is the normalized-Haar `L^p(T³)` slice. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- The torus `L^q(0,∞;L^p(T³))` extended norm. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- The periodic `L²(0,T;L²(T³))` extended norm. -/
def spaceTimeL2L2ENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (torusLift (fun x => z (t, x))) 2 periodicTorusMeasure) ^ (2 : ℝ))
    ^ ((2 : ℝ)⁻¹)

/-! ## U1--U3: arithmetic -/

theorem thresholdValue : criticalOrder 1 = (1 : ℝ) / 2 := by
  norm_num [criticalOrder]

theorem mixedRegionArithmetic :
    ∀ p q : ℝ≥0∞, 3 < 3 / p.toReal + 2 / q.toReal →
      0 < NSFormalization.Section3.T15.alphaT p q ∧
        0 < NSFormalization.Section3.T15.alphaT p q + 1 := by
  intro p q h
  rw [NSFormalization.Section3.T15.alphaT_formula]
  constructor <;> linarith

theorem regionExamples :
    0 < NSFormalization.Section3.T15.alphaT 2 1 ∧
      0 < NSFormalization.Section3.T15.alphaT (4 / 3) 2 := by
  norm_num [NSFormalization.Section3.T15.alphaT]

/-! ## U4: the finite-time `L²` embedding -/

theorem energyTimeEmbedding :
    ∀ T : ℝ, 0 < T → ∀ z : SpaceTimeField,
      spaceTimeL2L2ENormT T z ≤
        ENNReal.ofReal (Real.sqrt T) * energyEssSupT T z := by
  intro T hT z
  let h : ℝ → ℝ≥0∞ := fun t ↦
    eLpNorm (torusLift (fun x => z (t, x))) 2 periodicTorusMeasure
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) T)
  have hae : ∀ᵐ t ∂μ, h t ^ (2 : ℝ) ≤ (essSup h μ) ^ (2 : ℝ) := by
    filter_upwards [ENNReal.ae_le_essSup h] with t ht
    exact ENNReal.rpow_le_rpow ht (by norm_num)
  have hint : (∫⁻ t, h t ^ (2 : ℝ) ∂μ) ≤ (essSup h μ) ^ (2 : ℝ) * μ univ := by
    calc
      (∫⁻ t, h t ^ (2 : ℝ) ∂μ) ≤ ∫⁻ _t, (essSup h μ) ^ (2 : ℝ) ∂μ :=
        lintegral_mono_ae hae
      _ = (essSup h μ) ^ (2 : ℝ) * μ univ := by
        rw [lintegral_const]
  have hmeasure : μ univ = ENNReal.ofReal T := by
    simp only [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
    rw [sub_zero]
  unfold spaceTimeL2L2ENormT energyEssSupT
  change (∫⁻ t, h t ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) ≤ _
  calc
    (∫⁻ t, h t ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) ≤
        ((essSup h μ) ^ (2 : ℝ) * ENNReal.ofReal T) ^ ((2 : ℝ)⁻¹) :=
      ENNReal.rpow_le_rpow (hint.trans_eq (congrArg _ hmeasure)) (by positivity)
    _ = (essSup h μ) * ENNReal.ofReal (Real.sqrt T) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (2 : ℝ)⁻¹ = 1 by norm_num,
        ENNReal.rpow_one]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, Real.sqrt_eq_rpow,
        ← ENNReal.ofReal_rpow_of_nonneg hT.le (by positivity)]
    _ = ENNReal.ofReal (Real.sqrt T) * essSup h μ := mul_comm _ _

/-! ## U5: a smooth reference has finite energy -/

private theorem meanZero_periodicSobolevENorm_le {s : ℝ} {v : SpatialField}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s v A) :
    periodicSobolevENorm s (meanZeroPartT v) ≤ periodicSobolevENorm s v := by
  obtain ⟨B, hB, _hBzero⟩ := meanZero_datum s v A hA
  rw [periodicSobolevENorm_eq hB, periodicSobolevENorm_eq hA]
  rw [← ofReal_norm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hcomp (i : Fin 3) : ‖B.1 i‖ ≤ ‖A.1 i‖ := by
    have heq : B.1 i = A.1 i - lp.single 2 (0 : PeriodicFrequency) (A.1 i 0) := by
      ext k
      change B.1.1 i k = A.1.1 i k -
        ((lp.single 2 (0 : PeriodicFrequency) (A.1 i 0) : PeriodicScalarData)) k
      rw [hB.2.2 i k, hA.2.2 i k]
      have hi := hA.integrable_component i
      have hc : Integrable
          (torusLift (fun _ : Space ↦ ((meanT v i : ℝ) : ℂ)))
          periodicTorusMeasure := integrable_const _
      rw [show periodicFourierCoeff
          (fun x ↦ (((meanZeroPartT v x) i : ℝ) : ℂ)) k =
          periodicFourierCoeff
              (fun x ↦ ((v x i : ℝ) : ℂ) - ((meanT v i : ℝ) : ℂ)) k by
            congr 1
            funext x
            simp [meanZeroPartT]]
      rw [periodicFourierCoeff_sub hi hc k, periodicFourierCoeff_const]
      by_cases hk : k = 0
      · subst k
        rw [lp.single_apply_self, hA.2.2 i 0,
          periodicFourierCoeff_zero_eq_mean_component hA.2.1 i]
        simp [periodicFrequencyWeight]
      · rw [lp.single_apply_ne 2 0 _ hk]
        simp [hk]
    rw [heq]
    have hsq := lp.norm_compl_sum_single (p := (2 : ℝ≥0∞)) (by norm_num)
      (A.1 i) ({0} : Finset PeriodicFrequency)
    simp only [Finset.sum_singleton] at hsq
    norm_num at hsq
    nlinarith [norm_nonneg (A.1 i - lp.single 2 (0 : PeriodicFrequency) (A.1 i 0)),
      norm_nonneg (A.1 i), sq_nonneg ‖A.1 i 0‖]
  change ‖B.1‖ ≤ ‖A.1‖
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  gcongr with i
  nlinarith [norm_nonneg (B.1 i), norm_nonneg (A.1 i), hcomp i]

theorem referenceFiniteEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              energyENormT T reference.velocity < ⊤ := by
  intro a _ha ν _hν T hT g _hg δ hδ reference
  have hsub : Ioo (0 : ℝ) T ⊆ Ico (0 : ℝ) (T + δ) := by
    intro t ht
    exact ⟨ht.1.le, by linarith [ht.2]⟩
  have hs : ∀ t ∈ Ioo (0 : ℝ) T,
      ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ reference.velocity (t, x)) := by
    intro t ht
    exact reference.velocity_smooth.comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun x ↦ ⟨hsub ht, mem_univ x⟩)
  have hp : IsPeriodicOn (Ioo (0 : ℝ) T) reference.velocity :=
    fun t ht ↦ reference.velocity_periodic t (hsub ht)
  rw [energyENormT_eq T reference.velocity hs hp]
  apply ENNReal.add_lt_top.mpr
  constructor
  · obtain ⟨G, hG, hdatum⟩ := reference.sobolev 0
    obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ Icc (0 : ℝ) T, ‖G t‖ ≤ C :=
      isCompact_Icc.exists_bound_of_continuousOn
        (hG.mono fun t (ht : t ∈ Icc (0 : ℝ) T) ↦
          ⟨ht.1, by linarith [ht.2, hδ]⟩)
    apply lt_of_le_of_lt (essSup_le_of_ae_le (ENNReal.ofReal C) ?_)
      ENNReal.ofReal_lt_top
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hd : IsPeriodicDatum (0 : ℝ) (fun x ↦ reference.velocity (t, x)) (G t) := by
      convert hdatum t (hsub ht) using 1
      all_goals norm_num
    rw [periodicSobolevENorm_eq_datum hd, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC t ⟨ht.1.le, ht.2.le⟩)
  · obtain ⟨G, hG, hdatum⟩ := reference.sobolev 1
    obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ Icc (0 : ℝ) T, ‖G t‖ ≤ C :=
      isCompact_Icc.exists_bound_of_continuousOn
        (hG.mono fun t (ht : t ∈ Icc (0 : ℝ) T) ↦
          ⟨ht.1, by linarith [ht.2, hδ]⟩)
    have hpoint : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
        periodicHomogeneousENorm 1
            (meanZeroPartT (fun x ↦ reference.velocity (t, x))) ^ (2 : ℝ) ≤
          (ENNReal.ofReal C) ^ (2 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht' := hsub ht
      have hd : IsPeriodicDatum (1 : ℝ) (fun x ↦ reference.velocity (t, x)) (G t) := by
        convert hdatum t ht' using 1
        all_goals norm_num
      have hst := hs t ht
      have hpt : IsPeriodicSpatial (fun x ↦ reference.velocity (t, x)) :=
        reference.velocity_periodic t ht'
      have hmean := (mean_decomposition (fun x ↦ reference.velocity (t, x)) hpt
        ((memLp_torusLift_vector hst.continuous 1).integrable (by norm_num))).2
      have hhom : MemPeriodicHomogeneous 1
          (meanZeroPartT (fun x ↦ reference.velocity (t, x))) := by
        refine ⟨fun x i ↦ by simp only [meanZeroPartT, hpt x i],
          memLp_torusLift_vector (hst.sub contDiff_const).continuous 2, hmean, ?_⟩
        obtain ⟨A, hA⟩ := smooth_homogeneous_datum_one
          (hst.sub contDiff_const) (fun x i ↦ by simp only [hpt x i]) hmean
        unfold periodicHomogeneousENorm
        exact ne_top_of_le_ne_top enorm_ne_top (iInf_le_of_le ⟨A, hA⟩ le_rfl)
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      calc
        periodicHomogeneousENorm 1
            (meanZeroPartT (fun x ↦ reference.velocity (t, x))) ≤
            periodicSobolevENorm 1
              (meanZeroPartT (fun x ↦ reference.velocity (t, x))) :=
          homogeneous_le_sobolev 1 (by norm_num) _ hhom
        _ ≤ periodicSobolevENorm 1 (fun x ↦ reference.velocity (t, x)) :=
          meanZero_periodicSobolevENorm_le hd
        _ = ENNReal.ofReal ‖G t‖ := by
          rw [periodicSobolevENorm_eq_datum hd, ofReal_norm]
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hC t ⟨ht.1.le, ht.2.le⟩)
    unfold coefficientEnergyGradientT
    apply lt_of_le_of_lt (ENNReal.rpow_le_rpow (lintegral_mono_ae hpoint) (by positivity))
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioo, sub_zero]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
        ENNReal.ofReal_lt_top).ne

/-! ## U6: zero representatives -/

theorem torusForceSobolevENorm_zero (q : ℝ≥0∞) (s : ℝ) :
    forceSobolevENormT q s (0 : SpaceTimeField) = 0 := by
  apply le_antisymm _ bot_le
  have hzeroDatum : IsPeriodicDatum s (0 : SpatialField) (0 : PeriodicSobolev s) := by
    refine ⟨fun _ _ ↦ rfl, integrable_const 0, ?_⟩
    intro i k
    change (0 : ℂ) = (periodicFrequencyWeight k) ^ (s / 2) •
      periodicFourierCoeff (fun _ : Space ↦ (0 : ℂ)) k
    rw [periodicFourierCoeff_const]
    simp
  have hz : IsPeriodicSobolevPath s (0 : SpaceTimeField) (fun _ ↦ 0) := by
    intro _t _ht
    exact hzeroDatum
  refine (iInf_le _ ⟨fun _ ↦ 0, hz, aestronglyMeasurable_const⟩).trans ?_
  change eLpNorm (fun _ : ℝ ↦ (0 : PeriodicSobolev s)) q forceTimeMeasure ≤ 0
  have hfun : (fun _ : ℝ ↦ (0 : PeriodicSobolev s)) = 0 := rfl
  rw [hfun]
  exact le_of_eq (MeasureTheory.eLpNorm_zero (α := ℝ) (ε := PeriodicSobolev s)
    (p := q) (μ := forceTimeMeasure))

theorem torusMixedLebesgueENormT_zero (q p : ℝ≥0∞) [Fact (1 ≤ p)] :
    mixedLebesgueENormT q p (0 : SpaceTimeField) = 0 := by
  apply le_antisymm _ bot_le
  have hz : IsPeriodicLebesgueSlicePath p (0 : SpaceTimeField) (fun _ ↦ 0) := by
    intro _t _ht
    calc
      ((0 : Lp Space p periodicTorusMeasure) : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
          0 := Lp.coeFn_zero Space p periodicTorusMeasure
      _ =ᵐ[periodicTorusMeasure] torusLift (fun _x : Space ↦ (0 : Space)) := by
        filter_upwards with _y
        rfl
  refine (iInf_le _ ⟨fun _ ↦ 0, hz, aestronglyMeasurable_const⟩).trans ?_
  change eLpNorm (fun _ : ℝ ↦ (0 : Lp Space p periodicTorusMeasure)) q
    forceTimeMeasure ≤ 0
  have hfun : (fun _ : ℝ ↦ (0 : Lp Space p periodicTorusMeasure)) = 0 := rfl
  rw [hfun]
  exact le_of_eq (MeasureTheory.eLpNorm_zero (α := ℝ)
    (ε := Lp Space p periodicTorusMeasure) (p := q) (μ := forceTimeMeasure))

end NSFormalization.Section3.T19
