import NSFormalization.Section3.T19.DensityEngine

noncomputable section
namespace NSFormalization.Section3.T19
open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Section3.T10
open scoped ENNReal Topology ContDiff

/-- The energy functional only uses spatial slices at times in `(0,T)`. -/
theorem energyENormT_congr_Ico {T : ℝ} {u v : SpaceTimeField}
    (h : EqOn u v (Ico (0 : ℝ) T ×ˢ univ)) :
    energyENormT T u = energyENormT T v := by
  have hs (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      (fun x => u (t, x)) = (fun x => v (t, x)) :=
    funext fun x => h ⟨⟨ht.1.le, ht.2⟩, mem_univ x⟩
  unfold energyENormT energyEssSupT energyGradientT
  apply congrArg₂ (· + ·)
  · apply essSup_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [hs t ht]
  · apply congrArg (fun x : ℝ≥0∞ => x ^ ((2 : ℝ)⁻¹))
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [spatialGradient, spatialDerivative, hs t ht]

/-- Smooth slices supply the measurability needed for energy subadditivity. -/
theorem energySlices_of_smooth {T : ℝ} {u : SpaceTimeField}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ univ)) :
    NSFormalization.Section3.T15.EnergySlicesMemLpT T u := by
  have hs (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      ContDiff ℝ ∞ (fun x => u (t, x)) :=
    hu.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨⟨ht.1.le, ht.2⟩, mem_univ x⟩)
  constructor
  · intro t ht
    exact memLp_torusLift_vector (hs t ht).continuous 2
  · intro t ht
    exact memLp_gradientTensor (hs t ht)

/-- Reversing a difference leaves the physical energy norm unchanged. -/
theorem energyENormT_sub_comm (T : ℝ) (u v : SpaceTimeField) :
    energyENormT T (fun z => u z - v z) =
      energyENormT T (fun z => v z - u z) := by
  have hn (w : SpaceTimeField) : energyENormT T (fun z => -w z) = energyENormT T w := by
    have hg (t : ℝ) : (fun x => spatialGradient (fun z => -w z) t x) =
        -(fun x => spatialGradient w t x) := by
      funext x
      apply PiLp.ext
      intro i
      simp [spatialGradient, spatialDerivative]
    unfold energyENormT energyEssSupT energyGradientT
    have hn' {E : Type} [NormedAddCommGroup E] (f : Space → E) :
        eLpNorm (torusLift (fun x => -f x)) 2 periodicTorusMeasure =
        eLpNorm (torusLift f) 2 periodicTorusMeasure := by
      change eLpNorm (-(torusLift f)) 2 periodicTorusMeasure = _
      exact eLpNorm_neg _ _ _
    simp only [hg, Pi.neg_apply, hn']
  convert hn (fun z => v z - u z) using 1
  simp only [neg_sub]

/-- U13: one insertion family converges in both required topologies. -/
theorem simultaneousPairConvergence :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              ∃ ε₀ : ℝ, 0 < ε₀ ∧
                ∃ u f : ℝ → SpaceTimeField,
                  (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                    f ε ∈ forceClassT ∧
                    maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                    (∃ w : ClassicalSolutionT ν a (f ε) T, w.velocity = u ε) ∧
                    SingularTrajectoryT ν a T (u ε)) ∧
                  Tendsto
                    (fun ε : ℝ =>
                      energyENormT T (fun z => u ε z - reference.velocity z))
                    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) ∧
                  (∀ s : ℝ, s < 1 / 2 →
                    Tendsto
                      (fun ε : ℝ => forceSobolevENormT 1 s (fun z => f ε z - g z))
                      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))) := by
  intro a ha ν hν T hT g hg δ hδ reference
  let A := insertion hν ha hg hT hδ reference
  have href : ContDiffOn ℝ ∞ reference.velocity (Ico (0 : ℝ) T ×ˢ univ) :=
    reference.velocity_smooth.mono (by
      intro z hz
      exact ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩)
  have heq (ε : ℝ) :
      energyENormT T (fun z => A.velocity ε z - reference.velocity z) =
      energyENormT T (fun z => A.velocity ε z - (extendByZero reference).velocity z) := by
    apply energyENormT_congr_Ico
    intro z hz
    change A.velocity ε z - reference.velocity z =
      A.velocity ε z - (extendByZero reference).velocity z
    rw [extendByZero_velocity_eqOn reference
      (show z ∈ Ico (0 : ℝ) (T + δ) ×ˢ univ from
        ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩)]
  have hfinite (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) A.ε₀) :
      energyENormT T (fun z => A.velocity ε z - reference.velocity z) < ⊤ := by
    rw [heq]
    exact lt_of_le_of_lt (energyRate hν ha hg hT hδ reference ε hε)
      ENNReal.ofReal_lt_top
  refine ⟨A.ε₀, A.eps_pos, A.velocity, A.force, ?_, ?_, ?_⟩
  · intro ε hε
    have he : ε ∈ Ioc (0 : ℝ) A.ε₀ := ⟨hε.1, hε.2.le⟩
    obtain ⟨w, hw, _⟩ := solution hν ha hg hT hδ reference ε he
    have hws : ContDiffOn ℝ ∞ (A.velocity ε) (Ico (0 : ℝ) T ×ˢ univ) :=
      hw ▸ w.velocity_smooth
    refine ⟨A.force_mem ε he, A.lifespan ε he, ⟨w, hw⟩,
      A.force ε, A.force_mem ε he, ⟨w, hw⟩, ?_, A.blowup_limsup ε he⟩
    have htri := NSFormalization.Section3.T18.energyENormT_add_le
      (hws.sub href) href (energySlices_of_smooth (hws.sub href))
      (energySlices_of_smooth href)
    simp only [sub_add_cancel] at htri
    exact (lt_of_le_of_lt htri (ENNReal.add_lt_top.mpr
      ⟨hfinite ε he, referenceFiniteEnergy a ha ν hν T hT g hg δ hδ reference⟩)).ne
  · let M := (BlowupDensity.Bindings.packetImportFamily.select ν hν).energyBound +
      (BlowupDensity.Bindings.packetImportFamily.select ν hν).dissipationBound
    let C := (insertionData hν ha hg hT hδ reference).correction.energyConst
    have hp (b : ℝ) (hb : 0 < b) :
        Tendsto (fun ε : ℝ => ε ^ b) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq] using Filter.tendsto_id.rpow_const_nhds_zero hb
    have hr : Tendsto (fun ε : ℝ => M * ε ^ ((1 : ℝ) / 2) +
        C * ε ^ ((3 : ℝ) / 2)) (𝓝 0) (𝓝 0) := by
      simpa using ((hp _ (by norm_num)).const_mul M).add
        ((hp _ (by norm_num)).const_mul C)
    have hu := (ENNReal.tendsto_ofReal hr).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [ENNReal.ofReal_zero] at hu
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · exact Eventually.of_forall (fun _ => bot_le)
    · filter_upwards [Ioc_mem_nhdsGT A.eps_pos] with ε hε
      rw [heq]
      exact energyRate hν ha hg hT hδ reference ε hε
  · exact forceDifference_sobolev_tendsto hν ha hg hT hδ reference

/-- U14: every regular trajectory lies in the energy closure. -/
theorem closureInEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
              energyENormT T (fun z => u z - u' z) < r := by
  intro a ha ν hν T hT u hreg r hr
  obtain ⟨g, hg, δ, hδ, reference, rfl⟩ := hreg
  obtain ⟨ε₀, hε₀, U, F, hfamily, hconv, _⟩ :=
    simultaneousPairConvergence a ha ν hν T hT g hg δ hδ reference
  have hwindow : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) ε₀ :=
    Ioo_mem_nhdsGT hε₀
  obtain ⟨ε, hε, hd⟩ := (hwindow.and (hconv.eventually (gt_mem_nhds hr))).exists
  refine ⟨U ε, (hfamily ε hε).2.2.2, ?_⟩
  rwa [energyENormT_sub_comm]

end NSFormalization.Section3.T19
