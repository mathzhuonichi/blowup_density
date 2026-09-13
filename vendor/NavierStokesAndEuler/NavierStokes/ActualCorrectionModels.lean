import NavierStokes.OffplaneCorrectionExtensions
import NavierStokes.BaseContextAssembly
import NavierStokes.CommonBaseContext

/-!
# Positive-scale models of the actual correction seed

All coefficient sequences, cutoff schedules, and discrete phase parameters
in this file are those of the supplied `FinalSlowBase` and `Prepared` object.
The positive scale is a coordinate of the model, not a second chosen base.
-/

noncomputable section

namespace NavierStokes.ActualCorrectionModels

open Set Filter Function
open scoped Topology ContDiff InnerProductSpace

abbrev Slow := PhaseCalculus.Slow
abbrev Model := MeanRankUpdate.ModelPoint
abbrev Inner := SimilarityProfile.InnerPoint

noncomputable local instance : NormedAddCommGroup SmoothCovariance.Mat2 :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))
noncomputable local instance : NormedSpace ℝ SmoothCovariance.Mat2 :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))

noncomputable def modelDomain : Set Model := {y | 0 < y.1}
noncomputable def radialModelDomain : Set Model := {y | 0 < y.1 ∧ 0 < y.2.1}

theorem modelDomain_open : IsOpen modelDomain := isOpen_lt continuous_const continuous_fst
theorem radialModelDomain_open : IsOpen radialModelDomain :=
  modelDomain_open.inter (isOpen_lt continuous_const continuous_snd.fst)

/-- `(q,R,Z)` goes to the actual inner coordinates. -/
noncomputable def modelCoordinates (h : ℝ) (y : Model) : SlowBorelBase.Chart :=
  (y.1, (y.2.1 ^ 2 / 2 / y.1, y.2.2 / y.1 ^ CoordinateAlgebra.D h))

theorem modelCoordinates_smoothAt (h : ℝ) {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (modelCoordinates h) y := by
  exact contDiffAt_fst.prodMk
    ((((contDiffAt_snd.fst.pow 2).div_const 2).div contDiffAt_fst hy.ne').prodMk
      (contDiffAt_snd.snd.div (contDiffAt_fst.rpow_const_of_ne hy.ne')
        (Real.rpow_pos_of_pos hy _).ne'))

noncomputable def originalPoint (h : ℝ) (p : Slow) : Model :=
  (SimilarityHomogeneity.chartQ h p, (p.1, p.2.1))

noncomputable def stablePoint (h : ℝ) (p : Slow) : Model :=
  (OffplaneCorrectionExtensions.stableQ (2 * h) (p.2.2, p.2.1), (p.1, p.2.1))

noncomputable def stableDomain (h : ℝ) : Set Slow :=
  {p | (p.2.2, p.2.1) ∈ PositiveRepresentatives.stableTarget (2 * h)}

noncomputable def positiveStableDomain (h : ℝ) : Set Slow :=
  {p | p ∈ stableDomain h ∧ 0 < p.1}

theorem stableDomain_open (h : ℝ) : IsOpen (stableDomain h) :=
  (PositiveRepresentatives.stableTarget_open (2 * h)).preimage
    (continuous_snd.snd.prodMk continuous_snd.fst)

theorem positiveStableDomain_open (h : ℝ) : IsOpen (positiveStableDomain h) :=
  (stableDomain_open h).inter (isOpen_lt continuous_const continuous_fst)

theorem stablePoint_pos {h : ℝ} {p : Slow} (hp : p ∈ stableDomain h) :
    0 < (stablePoint h p).1 := OffplaneCorrectionExtensions.stableQ_pos hp

theorem stablePoint_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : p ∈ stableDomain h) : ContDiffAt ℝ ∞ (stablePoint h) p := by
  exact ((OffplaneCorrectionExtensions.stableQ_contDiffAt (by linarith) (by linarith) hp).comp p
    (contDiffAt_snd.snd.prodMk contDiffAt_snd.fst)).prodMk
      (contDiffAt_fst.prodMk contDiffAt_snd.fst)

theorem stablePoint_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : 0 < p.2.2) : stablePoint h p = originalPoint h p := by
  apply Prod.ext
  · exact OffplaneCorrectionExtensions.stableQ_eq_coordinateQ (by linarith) (by linarith) hp
  · rfl

theorem modelCoordinates_original (h : ℝ) (p : Slow) :
    modelCoordinates h (originalPoint h p) = BaseChartJets.normalizedCoordinates h p := by
  rw [BaseChartJets.normalizedCoordinates_eq]
  simp only [modelCoordinates, originalPoint, SimilarityHomogeneity.chartX,
    SimilarityHomogeneity.chartEta, SimilarityCoordinates.coordinateX,
    SimilarityCoordinates.coordinateEta, SimilarityHomogeneity.chartQ, CoordinateAlgebra.D]
  congr 3
  ring_nf

theorem positiveTime_mem_stable {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hp : 0 < p.2.2) : p ∈ stableDomain h :=
  PositiveRepresentatives.positiveTime_mem_stableTarget (by linarith) (by linarith) hp

theorem endpoint_mem_stable {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (R : ℝ) {Z : ℝ} (hZ : Z ≠ 0) : (R, (Z, 0)) ∈ stableDomain h :=
  EndpointCoordinates.zeroTime_mem_stableTarget (by linarith) (by linarith) hZ

/-- The literal cutoff series at positive scale, including its leading power. -/
noncomputable def scalarModel (a : ℕ → ℕ) (h b Q : ℝ) (f : ℕ → Inner → ℝ)
    (y : Model) : ℝ :=
  y.1 ^ b * SlowBorelBase.slowSum a h f
    (SlowBorelBase.scaleMap Q (modelCoordinates h y))

theorem scalarModel_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) (h b : ℝ)
    {Q : ℝ} (hQ : 0 < Q) {f : ℕ → Inner → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {y : Model} (hy : 0 < y.1) : ContDiffAt ℝ ∞ (scalarModel a h b Q f) y := by
  have hc := (SlowBorelBase.scaleMap Q).contDiff.contDiffAt.comp y (modelCoordinates_smoothAt h hy)
  have hs : ContDiffAt ℝ ∞ (SlowBorelBase.slowSum a h f)
      (SlowBorelBase.scaleMap Q (modelCoordinates h y)) := SlowBorelBase.slowSum_smoothAt ha hf h
    (show 0 < (SlowBorelBase.scaleMap Q (modelCoordinates h y)).1 from mul_pos hQ hy)
  exact (contDiffAt_fst.rpow_const_of_ne hy.ne').mul
    (ContDiffAt.comp (g := SlowBorelBase.slowSum a h f) y hs hc)

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

noncomputable def frequencyModel (n : ℕ) (y : Model) : ℝ :=
  y.1 ^ (-CoordinateAlgebra.A F.data.h) / y.2.1 *
    SlowBorelBase.normalizedSwirl (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
      (FinalSlowBase.coefficients H v)
      (SlowBorelBase.scaleMap (ChartScales.Q n) (modelCoordinates F.data.h y))

noncomputable def axialModel (n : ℕ) : Model → ℝ :=
  scalarModel (FinalSlowBase.scales H v upper B) F.data.h (-CoordinateAlgebra.A F.data.h)
    (ChartScales.Q n) (FinalSlowBase.coefficients H v).axial

noncomputable def streamModel (n : ℕ) : Model → ℝ :=
  scalarModel (FinalSlowBase.scales H v upper B) F.data.h (-CoordinateAlgebra.A F.data.h)
    (ChartScales.Q n) (BaseRadialJets.averageSequence (FinalSlowBase.coefficients H v))

noncomputable def frequency (n : ℕ) : Slow → ℝ := frequencyModel H v upper B n ∘ stablePoint F.data.h
noncomputable def axial (n : ℕ) : Slow → ℝ := axialModel H v upper B n ∘ stablePoint F.data.h
noncomputable def stream (n : ℕ) : Slow → ℝ := streamModel H v upper B n ∘ stablePoint F.data.h

noncomputable def radial (n : ℕ) (p : Slow) : ℝ :=
  -(ChartScales.epsilon F.data.h n * p.1 / 2) * PhaseCalculus.slowZ (stream H v upper B n) p

theorem frequencyModel_smoothAt (n : ℕ) {y : Model} (hy : y ∈ radialModelDomain) :
    ContDiffAt ℝ ∞ (frequencyModel H v upper B n) y := by
  have hc := (SlowBorelBase.scaleMap (ChartScales.Q n)).contDiff.contDiffAt.comp y
    (modelCoordinates_smoothAt F.data.h hy.1)
  have hs : ContDiffAt ℝ ∞ (SlowBorelBase.slowSum (FinalSlowBase.scales H v upper B)
      F.data.h (FinalSlowBase.coefficients H v).phi)
      (SlowBorelBase.scaleMap (ChartScales.Q n) (modelCoordinates F.data.h y)) :=
    SlowBorelBase.slowSum_smoothAt (FinalSlowBase.scales_strictMono H v upper B)
    (FinalSlowBase.coefficients_smooth H v).phi F.data.h
    (show 0 < (SlowBorelBase.scaleMap (ChartScales.Q n) (modelCoordinates F.data.h y)).1 from
      mul_pos (ChartScales.Q_pos n) hy.1)
  have hX : 0 < 2 * (SlowBorelBase.scaleMap (ChartScales.Q n) (modelCoordinates F.data.h y)).2.1 := by
    change 0 < 2 * (y.2.1 ^ 2 / 2 / y.1)
    exact mul_pos (by norm_num) (div_pos (div_pos (sq_pos_of_pos hy.2) (by norm_num)) hy.1)
  exact ((contDiffAt_fst.rpow_const_of_ne hy.1.ne').div contDiffAt_snd.fst hy.2.ne').mul
    ((((contDiffAt_const.mul hc.snd.fst).sqrt hX.ne').div_const W.axis.normalization).mul
      (ContDiffAt.comp (g := SlowBorelBase.slowSum (FinalSlowBase.scales H v upper B)
        F.data.h (FinalSlowBase.coefficients H v).phi) y hs hc))

theorem axialModel_smoothAt (n : ℕ) {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (axialModel H v upper B n) y :=
  scalarModel_smoothAt (FinalSlowBase.scales_strictMono H v upper B) _ _ (ChartScales.Q_pos n)
    (FinalSlowBase.coefficients_smooth H v).axial hy

theorem streamModel_smoothAt (n : ℕ) {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (streamModel H v upper B n) y :=
  scalarModel_smoothAt (FinalSlowBase.scales_strictMono H v upper B) _ _ (ChartScales.Q_pos n)
    (BaseRadialJets.averageSequence_smooth (FinalSlowBase.coefficients_smooth H v)) hy

theorem frequency_eq (n : ℕ) {p : Slow} (hp : 0 < p.2.2) :
    frequency H v upper B n p = BaseContextAssembly.frequencySlow H v upper B n p := by
  simp only [frequency, comp_apply, stablePoint_eq F.data.h_pos F.data.h_lt_half hp,
    frequencyModel, modelCoordinates_original]
  simp only [BaseContextAssembly.frequencySlow, BaseChartJets.frequency,
    BaseChartJets.frequencyFactor, BaseChartJets.axialFactor,
    BaseChartJets.normalizedCoordinates_eq, originalPoint]

theorem axial_eq (n : ℕ) {p : Slow} (hp : 0 < p.2.2) :
    axial H v upper B n p = BaseContextAssembly.axialSlow H v upper B n p := by
  simp only [axial, comp_apply, stablePoint_eq F.data.h_pos F.data.h_lt_half hp,
    axialModel, scalarModel, modelCoordinates_original]
  simp only [BaseContextAssembly.axialSlow, BaseChartJets.axial, BaseChartJets.axialFactor,
    BaseChartJets.normalizedCoordinates_eq, originalPoint]

theorem stream_eq (n : ℕ) {p : Slow} (hp : 0 < p.2.2) :
    stream H v upper B n p = BaseRadialJets.normalizedStream (FinalSlowBase.scales H v upper B)
      F.data.h (FinalSlowBase.coefficients H v) (ChartScales.Q n) p := by
  simp only [stream, comp_apply, stablePoint_eq F.data.h_pos F.data.h_lt_half hp,
    streamModel, scalarModel, modelCoordinates_original]
  simp only [BaseRadialJets.normalizedStream, BaseChartJets.axialFactor,
    BaseChartJets.normalizedCoordinates_eq, originalPoint]

theorem frequency_smoothAt (n : ℕ) {p : Slow} (hp : p ∈ positiveStableDomain F.data.h) :
    ContDiffAt ℝ ∞ (frequency H v upper B n) p :=
  (frequencyModel_smoothAt H v upper B n ⟨stablePoint_pos hp.1, hp.2⟩).comp p
    (stablePoint_smoothAt F.data.h_pos F.data.h_lt_half hp.1)

theorem axial_smoothAt (n : ℕ) {p : Slow} (hp : p ∈ stableDomain F.data.h) :
    ContDiffAt ℝ ∞ (axial H v upper B n) p :=
  (axialModel_smoothAt H v upper B n (stablePoint_pos hp)).comp p
    (stablePoint_smoothAt F.data.h_pos F.data.h_lt_half hp)

theorem stream_smoothAt (n : ℕ) {p : Slow} (hp : p ∈ stableDomain F.data.h) :
    ContDiffAt ℝ ∞ (stream H v upper B n) p :=
  (streamModel_smoothAt H v upper B n (stablePoint_pos hp)).comp p
    (stablePoint_smoothAt F.data.h_pos F.data.h_lt_half hp)

theorem radial_smoothAt (n : ℕ) {p : Slow} (hp : p ∈ stableDomain F.data.h) :
    ContDiffAt ℝ ∞ (radial H v upper B n) p := by
  have hs : ContDiffAt ℝ ∞ (PhaseCalculus.slowZ (stream H v upper B n)) p :=
    ((stream_smoothAt H v upper B n hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  exact (((contDiffAt_const.mul contDiffAt_fst).div_const 2).neg).mul hs

theorem frequency_germ (n : ℕ) {p : Slow} (hp : 0 < p.2.2) :
    frequency H v upper B n =ᶠ[𝓝 p] BaseContextAssembly.frequencySlow H v upper B n := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd.snd).mem_nhds hp] with y hy
  exact frequency_eq H v upper B n hy

theorem axial_germ (n : ℕ) {p : Slow} (hp : 0 < p.2.2) :
    axial H v upper B n =ᶠ[𝓝 p] BaseContextAssembly.axialSlow H v upper B n := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd.snd).mem_nhds hp] with y hy
  exact axial_eq H v upper B n hy

theorem radial_eq (n : ℕ) {p : Slow} (hp : 0 < p.2.2) :
    radial H v upper B n p = BaseContextAssembly.radialSlow H v upper B n p := by
  have he : stream H v upper B n =ᶠ[𝓝 p]
      BaseRadialJets.normalizedStream (FinalSlowBase.scales H v upper B)
        F.data.h (FinalSlowBase.coefficients H v) (ChartScales.Q n) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd.snd).mem_nhds hp] with y hy
    exact stream_eq H v upper B n hy
  rw [BaseContextAssembly.radialSlow, BaseRadialJets.radial_eq_stream
    (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half
    (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H v) hp]
  exact congrArg (fun L : Slow →L[ℝ] ℝ => -(ChartScales.epsilon F.data.h n * p.1 / 2) * L (0, (1, 0))) he.fderiv_eq

end ActualBase

section ActualTarget

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- The same leading stress, using its proved smooth coefficient extension. -/
noncomputable def targetModel (y : Model) : MovingFrameODE.Plane :=
  y.1 ^ (-CoordinateAlgebra.A F.data.h - 1 / 2) •
    !₂[(FinalSlowBase.coefficients H v).stressTheta 0 (modelCoordinates F.data.h y).2,
      (FinalSlowBase.coefficients H v).stressAxial 0 (modelCoordinates F.data.h y).2]

noncomputable def target : Slow → MovingFrameODE.Plane := targetModel H v ∘ stablePoint F.data.h

theorem targetModel_smoothAt {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (targetModel H v) y := by
  have hc := (modelCoordinates_smoothAt F.data.h hy).snd
  apply (contDiffAt_fst.rpow_const_of_ne hy.ne').smul
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · exact ((FinalSlowBase.coefficients_smooth H v).stressTheta 0).contDiffAt.comp y hc
  · exact ((FinalSlowBase.coefficients_smooth H v).stressAxial 0).contDiffAt.comp y hc

theorem target_smoothAt {p : Slow} (hp : p ∈ stableDomain F.data.h) :
    ContDiffAt ℝ ∞ (target H v) p :=
  (targetModel_smoothAt H v (stablePoint_pos hp)).comp p
    (stablePoint_smoothAt F.data.h_pos F.data.h_lt_half hp)

theorem target_eq {p : Slow} (hp : 0 < p.2.2) :
    target H v p = PrimaryTargetBounds.actualTarget v p := by
  have hq := BaseChartJets.normalizedCoordinates_q_pos F.data.h_pos F.data.h_lt_half hp
  have hX : 0 ≤ (BaseChartJets.normalizedCoordinates F.data.h p).2.1 := by
    rw [← modelCoordinates_original]
    apply div_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    simpa only [BaseChartJets.normalizedCoordinates_eq, originalPoint] using hq.le
  have heta := (BaseChartJets.normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half hp).le
  have hs := FinalSlowBase.leading_stress_eq H v hX heta
  have he : !₂[(FinalSlowBase.coefficients H v).stressTheta 0
        (BaseChartJets.normalizedCoordinates F.data.h p).2,
      (FinalSlowBase.coefficients H v).stressAxial 0
        (BaseChartJets.normalizedCoordinates F.data.h p).2] =
      ProfileSpectralCone.stressVector v.profiles F.data.h
        (BaseChartJets.normalizedCoordinates F.data.h p).2 := by
    ext i
    fin_cases i
    · exact congrArg Prod.fst hs
    · exact congrArg Prod.snd hs
  change targetModel H v (stablePoint F.data.h p) = _
  rw [stablePoint_eq F.data.h_pos F.data.h_lt_half hp]
  unfold targetModel
  rw [modelCoordinates_original, he]
  simp only [PrimaryTargetBounds.actualTarget, BaseChartJets.normalizedCoordinates_eq, originalPoint]

theorem target_germ {p : Slow} (hp : 0 < p.2.2) :
    target H v =ᶠ[𝓝 p] PrimaryTargetBounds.actualTarget v := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd.snd).mem_nhds hp] with y hy
  exact target_eq H v hy

end ActualTarget

section LocalCalculus

theorem directional_smoothOn {U : Set Slow} (hU : IsOpen U) {f : Slow → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (d : Slow) :
    ContDiffOn ℝ ∞ (fun p => fderiv ℝ f p d) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem normal_eq_of_germs (epsilon p pz x0 theta slot : ℝ) {f g f' g' : Slow → ℝ}
    {s : Slow} (hf : f =ᶠ[𝓝 s] f') (hg : g =ᶠ[𝓝 s] g') :
    PhaseCalculus.phaseNormal epsilon p pz x0 f g (s, (theta, slot)) =
      PhaseCalculus.phaseNormal epsilon p pz x0 f' g' (s, (theta, slot)) := by
  have he : PhaseCalculus.phase epsilon p pz x0 f g =ᶠ[𝓝 (s, (theta, slot))]
      PhaseCalculus.phase epsilon p pz x0 f' g' := by
    filter_upwards [hf.comp_tendsto continuousAt_fst, hg.comp_tendsto continuousAt_fst] with y hyf hyg
    simp only [comp_apply] at hyf hyg
    simp only [PhaseCalculus.phase, hyf, hyg]
  simp only [PhaseCalculus.phaseNormal, he.fderiv_eq]

theorem normal_smoothOn {U : Set Slow} (hU : IsOpen U)
    {f g : Slow → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (epsilon p pz x0 theta : ℝ) (hepsilon : epsilon ≠ 0) (hR : ∀ s ∈ U, s.1 ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : Slow × ℝ =>
      PhaseCalculus.phaseNormal epsilon p pz x0 f g (z.1, (theta, z.2))) (U ×ˢ univ) := by
  have hfr : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowR f z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hf (1, (0, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  have hgr : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowR g z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hg (1, (0, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  have hfz : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowZ f z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hf (0, (1, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  have hgz : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowZ g z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hg (0, (1, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  have hex : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseEstimates.explicitNormal epsilon p pz x0
      z.1.1 z.2 (PhaseCalculus.slowR f z.1) (PhaseCalculus.slowR g z.1)
      (PhaseCalculus.slowZ f z.1) (PhaseCalculus.slowZ g z.1)) (U ×ˢ univ) := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiffOn_const.sub (contDiffOn_snd.mul ((contDiffOn_const.mul hfr).add (contDiffOn_const.mul hgr)))
    · exact contDiffOn_const.div contDiffOn_fst.fst (fun z hz => hR _ hz.1)
    · exact contDiffOn_const.sub ((contDiffOn_const.mul contDiffOn_snd).mul
        ((contDiffOn_const.mul hfz).add (contDiffOn_const.mul hgz)))
  apply hex.congr
  intro z hz
  exact (PhaseEstimates.phaseNormal_eq_explicit epsilon p pz x0 f g (z.1, (theta, z.2)) hepsilon
    ((hf.contDiffAt (hU.mem_nhds hz.1)).differentiableAt (by simp))
    ((hg.contDiffAt (hU.mem_nhds hz.1)).differentiableAt (by simp)))

theorem normalVelocity_smoothOn {U : Set Slow} (hU : IsOpen U)
    {f g : Slow → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (epsilon p pz : ℝ) :
    ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.normalSlotDerivative epsilon p pz f g z.1)
      (U ×ˢ univ) := by
  have hfr : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowR f z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hf (1, (0, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  have hgr : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowR g z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hg (1, (0, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  have hfz : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowZ f z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hf (0, (1, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  have hgz : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowZ g z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hg (0, (1, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact ((contDiffOn_const.mul hfr).add (contDiffOn_const.mul hgr)).neg
  · exact contDiffOn_const
  · exact contDiffOn_const.neg.mul ((contDiffOn_const.mul hfz).add (contDiffOn_const.mul hgz))

theorem shear_smoothOn {U : Set Slow} (hU : IsOpen U)
    {f g : Slow → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseEstimates.shearVector f g z.1) (U ×ˢ univ) := by
  have hfr : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowR f z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hf (1, (0, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  have hgr : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => PhaseCalculus.slowR g z.1) (U ×ˢ univ) :=
    (directional_smoothOn hU hg (1, (0, 0))).comp contDiffOn_fst (fun _ hz => hz.1)
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiffOn_fst.fst.mul hfr
  · exact hgr

/-- Derive every geometric frame coefficient from the actual normal and
normal motion.  There is no regularity assumption on a frame output. -/
theorem frameFromNormal_smooth {U : Set (Slow × ℝ)} (hU : IsOpen U)
    {n nd : Slow × ℝ → MovingFrameODE.Space} {f : Slow × ℝ → ℝ}
    {g : Slow × ℝ → MovingFrameODE.Plane} {lam c rate nu : Slow × ℝ → ℝ}
    (hn : ContDiffOn ℝ ∞ n U) (hd : ContDiffOn ℝ ∞ nd U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hlam : ContDiffOn ℝ ∞ lam U) (hc : ContDiffOn ℝ ∞ c U)
    (hrate : ContDiffOn ℝ ∞ rate U) (hnu : ContDiffOn ℝ ∞ nu U)
    (hne : ∀ z ∈ U, MovingFrameODE.tail (n z) ≠ 0)
    (hcne : ∀ z ∈ U, c z ≠ 0) :
    (PrimaryODE.FrameData.ofNormalLocal n nd f g lam c rate nu).SmoothOn U := by
  have hb : ContDiffOn ℝ ∞ (fun z => MovingFrameODE.normalScale (n z)) U := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_normalScale (hn.contDiffAt (hU.mem_nhds hz)) (hne z hz)).contDiffWithinAt
  have hbn : ∀ z ∈ U, MovingFrameODE.normalScale (n z) ≠ 0 :=
    fun z hz => (MovingFrameODE.normalScale_pos (hne z hz)).ne'
  have hr : ContDiffOn ℝ ∞ (fun z => MovingFrameODE.radialSlope (n z)) U := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_radialSlope (hn.contDiffAt (hU.mem_nhds hz)) (hne z hz)).contDiffWithinAt
  have hk : ContDiffOn ℝ ∞ (fun z => MovingFrameODE.normalDirection (n z)) U := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_normalDirection (hn.contDiffAt (hU.mem_nhds hz)) (hne z hz)).contDiffWithinAt
  have hN := MovingFrameODE.quarterTurn.contDiff.comp_contDiffOn hk
  have htn := MovingFrameODE.tailCLM.contDiff.comp_contDiffOn hn
  have htd := MovingFrameODE.tailCLM.contDiff.comp_contDiffOn hd
  have hrd := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).contDiff.comp_contDiffOn hd
  have hbd : ContDiffOn ℝ ∞ (fun z => PhaseEstimates.scaleDerivative (n z) (nd z)) U :=
    (htn.inner ℝ htd).div hb hbn
  have hrdot : ContDiffOn ℝ ∞ (fun z => PhaseEstimates.slopeDerivative (n z) (nd z)) U :=
    (hrd.sub (hr.mul hbd)).div hb hbn
  have hkd : ContDiffOn ℝ ∞ (fun z => PhaseEstimates.directionDerivative (n z) (nd z)) U :=
    (hb.inv hbn).smul (htd.sub (hbd.smul hk))
  refine ⟨hb, hbd, hr, hrdot, hN.inner ℝ hkd, hf, hg, ?_, hlam, hc, hrate, ?_, hcne⟩
  · intro i
    fin_cases i
    · apply hk.congr
      intro z hz
      simp only [PrimaryODE.FrameData.ofNormalLocal, PrimaryODE.localFrame_eq (hne z hz)]
      exact MovingFrameODE.normalFrame_zero _ _
    · apply hN.congr
      intro z hz
      simp only [PrimaryODE.FrameData.ofNormalLocal, PrimaryODE.localFrame_eq (hne z hz)]
      exact MovingFrameODE.normalFrame_one _ _
  · have hv := hnu.mul (hn.inner ℝ hn)
    simp only [real_inner_self_eq_norm_sq] at hv
    exact hv

theorem referenceFunctions_smooth (lam c u L : ℝ) :
    ContDiff ℝ ∞ (fun z : Slow × ℝ => ViscousPropagator.referenceEigenvalue lam u L z.2) ∧
    ContDiff ℝ ∞ (fun z : Slow × ℝ => PrimaryODE.referenceProfile c u L z.2) ∧
    ContDiff ℝ ∞ (fun z : Slow × ℝ => PrimaryODE.referenceProfileRate u L z.2) := by
  have hs : ContDiff ℝ ∞ (fun z : Slow × ℝ => PulseGrowth.slotMagnitude u L z.2) := by
    unfold PulseGrowth.slotMagnitude
    exact contDiff_const.add ((contDiff_const.mul contDiff_snd).div_const L)
  have hD : ContDiff ℝ ∞ (fun z : Slow × ℝ => (1 : ℝ) + PulseGrowth.slotMagnitude u L z.2 ^ 2) :=
    contDiff_const.add (hs.pow 2)
  have hDn : ∀ z : Slow × ℝ, (1 : ℝ) + PulseGrowth.slotMagnitude u L z.2 ^ 2 ≠ 0 := fun z => by positivity
  have hr := hD.sqrt hDn
  refine ⟨contDiff_const.div hr (fun z => (Real.sqrt_pos.mpr (by positivity)).ne'),
    contDiff_const.mul hr, (hs.mul contDiff_const).div hD hDn⟩

theorem ambient_smooth {U : Set (Slow × ℝ)} {d : PrimaryODE.FrameData Slow}
    (hd : d.SmoothOn U) {w : Slow × ℝ → MovingFrameODE.Plane} (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun z => d.ambient z (w z)) U := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).contDiff.comp_contDiffOn hw
  have h1 := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1).contDiff.comp_contDiffOn hw
  exact MovingFrameODE.packCLM.contDiff.comp_contDiffOn
    ((h0.add h1).prodMk (((hd.rho.neg.mul (h0.add h1)).smul (hd.frame 0)).add
      ((hd.eigenvector.mul (h0.sub h1)).smul (hd.frame 1))))

end LocalCalculus

section ActualODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem pathFamily_eq_of_fiber {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F G : P × ℝ → E} {p : P} (he : ∀ t, F (p, t) = G (p, t)) (a b : ℝ) :
    SmoothPathFamily.pathFamily (a := a) (b := b) F p = SmoothPathFamily.pathFamily G p := by
  have hs : (fun t : Icc a b => F (p, t)) = (fun t : Icc a b => G (p, t)) :=
    funext fun t => he t
  by_cases hc : Continuous (fun t : Icc a b => F (p, t))
  · have hg : Continuous (fun t : Icc a b => G (p, t)) := by rwa [← hs]
    apply ContinuousMap.ext
    intro t
    rw [SmoothPathFamily.pathFamily_apply F p hc, SmoothPathFamily.pathFamily_apply G p hg, he]
  · have hg : ¬ Continuous (fun t : Icc a b => G (p, t)) := by rwa [← hs]
    simp only [SmoothPathFamily.pathFamily, dite_eq_right hc, dite_eq_right hg]

/-- Actual anchored Volterra solutions agree when their primitive data
agree on the entire slow fiber. -/
theorem reparamSolution_eq_of_fiber {A A' : Slow × ℝ → E →L[ℝ] E}
    {f f' : Slow × ℝ → E} {x x' : Slow → E} {p : Slow}
    (hA : ∀ t, A (p, t) = A' (p, t)) (hf : ∀ t, f (p, t) = f' (p, t))
    (hx : x p = x' p) (a t : ℝ) :
    JointODE.reparamSolution a A x f (p, t) = JointODE.reparamSolution a A' x' f' (p, t) := by
  have hAc : ∀ s, JointODE.rescale a A ((p, t), s) = JointODE.rescale a A' ((p, t), s) := by
    intro s
    simp only [JointODE.rescale, JointODE.timeMap, hA]
  have hfc : ∀ s, JointODE.rescale a f ((p, t), s) = JointODE.rescale a f' ((p, t), s) := by
    intro s
    simp only [JointODE.rescale, JointODE.timeMap, hf]
  unfold JointODE.reparamSolution SmoothPathFamily.odeFamily
  rw [pathFamily_eq_of_fiber hAc, pathFamily_eq_of_fiber hfc]
  dsimp only
  rw [hx]

/-- If the primitive coefficient is smooth for all slot times, the same
reparameterized solution is smooth for both signs of the terminal slot. -/
theorem reparamSolution_smooth {U : Set Slow} (hU : IsOpen U)
    {A : Slow × ℝ → E →L[ℝ] E} {f : Slow × ℝ → E} {x : Slow → E}
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ univ)) (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (hx : ContDiffOn ℝ ∞ x U) (a : ℝ) :
    ContDiffOn ℝ ∞ (JointODE.reparamSolution a A x f) (U ×ˢ univ) := by
  have hmap : MapsTo (JointODE.timeMap a) ((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ))
      (U ×ˢ (univ : Set ℝ)) := fun z hz => ⟨hz.1.1, mem_univ _⟩
  have hpath := SmoothPathFamily.contDiffOn_odeFamily_of_joint (a := (0 : ℝ)) (b := 1) zero_le_one
    (U ×ˢ (univ : Set ℝ)) univ (hU.prod isOpen_univ) isOpen_univ (subset_univ _)
    (JointODE.rescale a A) (fun p : Slow × ℝ => x p.1) (JointODE.rescale a f)
    (JointODE.rescale_contDiffOn A hA hmap)
    (hx.comp contDiffOn_fst (fun _ hz => hz.1)) (JointODE.rescale_contDiffOn f hf hmap)
  exact (ContinuousMap.evalCLM ℝ (⟨1, zero_le_one, le_rfl⟩ : Icc (0 : ℝ) 1)).contDiff.comp_contDiffOn hpath

end ActualODE

section SelectedPhase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0) (hr0 : 0 < r0)

/-- Keep the supplied representatives and all their rounded frequencies;
only the two continuous base fields are evaluated on their stable branch. -/
noncomputable def phase (j : Fin 2) : PhaseJetBounds.PhaseFamily (PrimaryGeometryAssembly.Index W a.N) :=
  { (PrimaryGeometryAssembly.construction H v a hr0 j).phase with
    F := fun L => frequency H v upper B (BaseChartJets.cellBand L)
    G := fun L => axial H v upper B (BaseChartJets.cellBand L) }

theorem phase_normal_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    {p : Slow} (hp : 0 < p.2.2) (s : ℝ) :
    (phase H v a hr0 j).normal L (p, s) =
      (PrimaryGeometryAssembly.construction H v a hr0 j).phase.normal L (p, s) :=
  normal_eq_of_germs _ _ _ _ _ _ (frequency_germ H v upper B _ hp) (axial_germ H v upper B _ hp)

theorem phase_velocity_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    {p : Slow} (hp : 0 < p.2.2) (s : ℝ) :
    (phase H v a hr0 j).velocity L (p, s) =
      (PrimaryGeometryAssembly.construction H v a hr0 j).phase.velocity L (p, s) := by
  have hf := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (frequency_germ H v upper B (BaseChartJets.cellBand L) hp)
  have hg := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (axial_germ H v upper B (BaseChartJets.cellBand L) hp)
  simp only [PhaseJetBounds.PhaseFamily.velocity, phase, PhaseCalculus.normalSlotDerivative,
    PhaseCalculus.slowR, PhaseCalculus.slowZ, hf, hg]
  rfl

theorem phase_shear_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    {p : Slow} (hp : 0 < p.2.2) (s : ℝ) :
    (phase H v a hr0 j).shear L (p, s) =
      (PrimaryGeometryAssembly.construction H v a hr0 j).phase.shear L (p, s) := by
  have hf := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (frequency_germ H v upper B (BaseChartJets.cellBand L) hp)
  have hg := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (axial_germ H v upper B (BaseChartJets.cellBand L) hp)
  simp only [PhaseJetBounds.PhaseFamily.shear, phase, PhaseEstimates.shearVector,
    PhaseCalculus.slowR, hf, hg]
  rfl

theorem phase_normal_smooth (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    ContDiffOn ℝ ∞ ((phase H v a hr0 j).normal L) (positiveStableDomain F.data.h ×ˢ univ) := by
  apply normal_smoothOn (positiveStableDomain_open F.data.h)
    (fun _ hp => (frequency_smoothAt H v upper B _ hp).contDiffWithinAt)
    (fun _ hp => (axial_smoothAt H v upper B _ hp.1).contDiffWithinAt)
  · exact (ChartScales.epsilon_pos F.data.h (BaseChartJets.cellBand L)).ne'
  · exact fun p hp => hp.2.ne'

theorem phase_velocity_smooth (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    ContDiffOn ℝ ∞ ((phase H v a hr0 j).velocity L) (positiveStableDomain F.data.h ×ˢ univ) :=
  normalVelocity_smoothOn (positiveStableDomain_open F.data.h)
    (fun _ hp => (frequency_smoothAt H v upper B _ hp).contDiffWithinAt)
    (fun _ hp => (axial_smoothAt H v upper B _ hp.1).contDiffWithinAt) _ _ _

theorem phase_shear_smooth (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    ContDiffOn ℝ ∞ ((phase H v a hr0 j).shear L) (positiveStableDomain F.data.h ×ˢ univ) :=
  shear_smoothOn (positiveStableDomain_open F.data.h)
    (fun _ hp => (frequency_smoothAt H v upper B _ hp).contDiffWithinAt)
    (fun _ hp => (axial_smoothAt H v upper B _ hp.1).contDiffWithinAt)

theorem phase_p_ne_zero (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    (phase H v a hr0 j).p L ≠ 0 := by
  intro hz
  have he := PrimaryGeometryAssembly.carrier_mul_phase_p H v a hr0 j L
  change (ChartScales.carrier F.data.h (BaseChartJets.cellBand L) : ℝ) *
    (phase H v a hr0 j).p L = _ at he
  rw [hz, mul_zero] at he
  exact PrimaryGeometryAssembly.angularMode_ne_zero H v a j L (Int.cast_eq_zero.mp he.symm)

theorem phase_normal_tail_ne_zero (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    {z : Slow × ℝ} (hz : z ∈ positiveStableDomain F.data.h ×ˢ (univ : Set ℝ)) :
    MovingFrameODE.tail ((phase H v a hr0 j).normal L z) ≠ 0 := by
  have hf := (frequency_smoothAt H v upper B (BaseChartJets.cellBand L) hz.1).differentiableAt (by simp)
  have hg := (axial_smoothAt H v upper B (BaseChartJets.cellBand L) hz.1.1).differentiableAt (by simp)
  have he := PhaseCalculus.phaseNormal_formula ((phase H v a hr0 j).epsilon L)
    ((phase H v a hr0 j).p L) ((phase H v a hr0 j).pz L) ((phase H v a hr0 j).x0 L)
    ((phase H v a hr0 j).F L) ((phase H v a hr0 j).G L)
    (z.1, ((phase H v a hr0 j).theta L, z.2))
    (show (phase H v a hr0 j).epsilon L ≠ 0 from
      (ChartScales.epsilon_pos F.data.h (BaseChartJets.cellBand L)).ne') hf hg
  change MovingFrameODE.tail (PhaseCalculus.phaseNormal _ _ _ _ _ _ _) ≠ 0
  rw [he]
  intro hh
  have hz0 := congrArg (fun w : MovingFrameODE.Plane => w 0) hh
  exact div_ne_zero (phase_p_ne_zero H v a hr0 j L) hz.1.2.ne' hz0

noncomputable def frame (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) : PrimaryODE.FrameData Slow :=
  let P := PrimaryGeometryAssembly.construction H v a hr0 j
  (phase H v a hr0 j).frameData P.lam P.c0 P.u P.L P.viscosity L

theorem frame_smooth (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    (frame H v a hr0 j L).SmoothOn (positiveStableDomain F.data.h ×ˢ univ) := by
  let P := PrimaryGeometryAssembly.construction H v a hr0 j
  have href := referenceFunctions_smooth (P.lam L) (P.c0 L) (P.u L) (P.L L)
  have hfreq : ContDiffOn ℝ ∞ (frequency H v upper B (BaseChartJets.cellBand L))
      (positiveStableDomain F.data.h) := fun _ hp => (frequency_smoothAt H v upper B _ hp).contDiffWithinAt
  apply frameFromNormal_smooth ((positiveStableDomain_open F.data.h).prod isOpen_univ)
    (phase_normal_smooth H v a hr0 j L) (phase_velocity_smooth H v a hr0 j L)
    (show ContDiffOn ℝ ∞ (fun z : Slow × ℝ => frequency H v upper B (BaseChartJets.cellBand L) z.1)
      (positiveStableDomain F.data.h ×ˢ univ) from
      hfreq.comp contDiffOn_fst (fun _ hz => hz.1))
    (phase_shear_smooth H v a hr0 j L) href.1.contDiffOn href.2.1.contDiffOn
    href.2.2.contDiffOn contDiffOn_const
    (fun _ hz => phase_normal_tail_ne_zero H v a hr0 j L hz)
  intro z hz
  change P.c0 L * Real.sqrt (1 + PulseGrowth.slotMagnitude (P.u L) (P.L L) z.2 ^ 2) ≠ 0
  apply mul_ne_zero
  · have hb := (P.c0_bound L).1
    exact abs_pos.mp (P.b_pos.trans_le hb)
  · exact (Real.sqrt_pos.mpr (by positivity)).ne'

theorem frame_coefficient_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (mode : ℤ) {p : Slow} (hp : 0 < p.2.2) (s : ℝ) :
    (frame H v a hr0 j L).coefficient mode (p, s) =
      ((PrimaryGeometryAssembly.construction H v a hr0 j).frame L).coefficient mode (p, s) := by
  have hF : (phase H v a hr0 j).F L p =
      (PrimaryGeometryAssembly.construction H v a hr0 j).phase.F L p := frequency_eq H v upper B _ hp
  simp only [frame, PrimaryPulseBounds.PhaseConstruction.frame, PhaseJetBounds.PhaseFamily.frameData,
    PrimaryODE.FrameData.coefficient, PrimaryODE.FrameData.damping,
    PrimaryODE.FrameData.error11, PrimaryODE.FrameData.error12, PrimaryODE.FrameData.error21,
    PrimaryODE.FrameData.error22, PrimaryODE.FrameData.errorA, PrimaryODE.FrameData.errorB,
    PrimaryODE.FrameData.errorC, PrimaryODE.FrameData.ofNormalLocal,
    phase_normal_eq H v a hr0 j L hp s, phase_velocity_eq H v a hr0 j L hp s,
    phase_shear_eq H v a hr0 j L hp s, hF]

theorem frame_ambient_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    {p : Slow} (hp : 0 < p.2.2) (s : ℝ) (w : MovingFrameODE.Plane) :
    (frame H v a hr0 j L).ambient (p, s) w =
      ((PrimaryGeometryAssembly.construction H v a hr0 j).frame L).ambient (p, s) w := by
  simp only [frame, PrimaryPulseBounds.PhaseConstruction.frame, PhaseJetBounds.PhaseFamily.frameData,
    PrimaryODE.FrameData.ambient, PrimaryODE.FrameData.ofNormalLocal,
    phase_normal_eq H v a hr0 j L hp s]

noncomputable def pulse (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    Slow × ℝ → MovingFrameODE.Space :=
  let P := PrimaryGeometryAssembly.construction H v a hr0 j
  PrimaryPulseBounds.normalizedPulse (frame H v a hr0 j L) (P.lam L) (P.u L) (P.L L)

theorem fundamental_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    {p : Slow} (hp : 0 < p.2.2) (s : ℝ) :
    let P := PrimaryGeometryAssembly.construction H v a hr0 j
    PrimaryPulseBounds.fundamental (frame H v a hr0 j L) (P.lam L) (P.u L) (P.L L) (p, s) =
      PrimaryPulseBounds.fundamental (P.frame L) (P.lam L) (P.u L) (P.L L) (p, s) := by
  exact reparamSolution_eq_of_fiber (fun t => frame_coefficient_eq H v a hr0 j L 1 hp t)
    (fun _ => rfl) rfl 0 s

theorem pulse_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    {p : Slow} (hp : 0 < p.2.2) (s : ℝ) :
    let P := PrimaryGeometryAssembly.construction H v a hr0 j
    pulse H v a hr0 j L (p, s) = PrimaryPulseBounds.normalizedPulse (P.frame L)
      (P.lam L) (P.u L) (P.L L) (p, s) := by
  dsimp only [pulse, PrimaryPulseBounds.normalizedPulse]
  rw [fundamental_eq H v a hr0 j L hp, frame_ambient_eq H v a hr0 j L hp]

theorem fundamental_smooth (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    let P := PrimaryGeometryAssembly.construction H v a hr0 j
    ContDiffOn ℝ ∞ (PrimaryPulseBounds.fundamental (frame H v a hr0 j L)
      (P.lam L) (P.u L) (P.L L)) (positiveStableDomain F.data.h ×ˢ univ) :=
  reparamSolution_smooth (positiveStableDomain_open F.data.h)
    ((frame_smooth H v a hr0 j L).coefficient 1) contDiffOn_const contDiffOn_const 0

theorem pulse_smooth (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N) :
    ContDiffOn ℝ ∞ (pulse H v a hr0 j L) (positiveStableDomain F.data.h ×ˢ univ) := by
  let P := PrimaryGeometryAssembly.construction H v a hr0 j
  have hc : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => (z.1, P.L L * z.2))
      (positiveStableDomain F.data.h ×ˢ univ) :=
    contDiffOn_fst.prodMk (contDiffOn_const.mul contDiffOn_snd)
  exact (ambient_smooth (frame_smooth H v a hr0 j L) (fundamental_smooth H v a hr0 j L)).comp hc
    (fun z hz => ⟨hz.1, mem_univ _⟩)

/-- The same native Haar, temporal-stretch, and slot-length prefactor. -/
noncomputable def covariance (vr vt : TorusInverse.Plane)
    (L : PrimaryGeometryAssembly.Index W a.N) (p : Slow) : SmoothCovariance.Mat2 :=
  fun r c => (PartitionedCovariance.nativePrefactor vr vt r0 *
    ChartScales.timeCoefficient F.data.h (BaseChartJets.cellBand L) *
      ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L)) *
    ∫ t in (1 / 10 : ℝ)..(9 / 10 : ℝ), GaussianTailFlat.profile t ^ 2 *
      (pulse H v a hr0 c L (p, t) 0 * pulse H v a hr0 c L (p, t) r.succ)

theorem covariance_eq (vr vt : TorusInverse.Plane) (L : PrimaryGeometryAssembly.Index W a.N)
    {p : Slow} (hp : 0 < p.2.2) :
    covariance H v a hr0 vr vt L p = PrimaryTargetBounds.preparedCovariance H v a vr vt L p := by
  rw [PrimaryTargetBounds.preparedCovariance_eq_construction H v a vr vt hr0]
  funext r c
  unfold covariance PrimaryPulseBounds.primaryCovariance PrimaryPulseBounds.covarianceMatrix
  simp_rw [pulse_eq H v a hr0 c L hp]

theorem covariance_smooth (vr vt : TorusInverse.Plane) (L : PrimaryGeometryAssembly.Index W a.N) :
    ContDiffOn ℝ ∞ (covariance H v a hr0 vr vt L) (positiveStableDomain F.data.h) := by
  apply contDiffOn_pi.mpr
  intro r
  apply contDiffOn_pi.mpr
  intro c
  have hp := pulse_smooth H v a hr0 c L
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).contDiff.comp_contDiffOn hp
  have hi := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) r.succ).contDiff.comp_contDiffOn hp
  have hg : ContDiffOn ℝ ∞ (fun z : Slow × ℝ => GaussianTailFlat.profile z.2 ^ 2)
      (positiveStableDomain F.data.h ×ˢ univ) :=
    ((GaussianTailFlat.profile_contDiff.comp contDiff_snd).pow 2).contDiffOn
  exact contDiffOn_const.mul (ParametricRephase.intervalIntegral_contDiffOn_of_joint _ _
    (positiveStableDomain_open F.data.h) (hg.mul (h0.mul hi)) (1 / 10) (9 / 10) (by norm_num))

/-- The actual periodic clock is retained as data; only its smooth slow
coefficient is evaluated on the stable branch. -/
noncomputable def periodicPhase (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (g : CommonCoverSolve.Geometry) (w : PeriodicPhaseAssembly.ClockWindow) :
    Slow × TorusInverse.Plane → ℝ :=
  let P := phase H v a hr0 j
  PeriodicPhaseAssembly.phase g w.cutoff
    (fun p => P.pz L / P.epsilon L * p.2.1 + P.x0 L * p.1)
    (fun p => P.p L * P.F L p + P.pz L * P.G L p)

theorem periodicPhase_smooth (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (g : CommonCoverSolve.Geometry) (w : PeriodicPhaseAssembly.ClockWindow) :
    ContDiffOn ℝ ∞ (periodicPhase H v a hr0 j L g w)
      (positiveStableDomain F.data.h ×ˢ univ) := by
  dsimp only [periodicPhase]
  apply PeriodicPhaseAssembly.phase_contDiffOn g w
  · exact (contDiffOn_const.mul contDiffOn_snd.fst).add (contDiffOn_const.mul contDiffOn_fst)
  · apply (contDiffOn_const.mul _).add (contDiffOn_const.mul _)
    · exact fun p hp => (frequency_smoothAt H v upper B _ hp).contDiffWithinAt
    · exact fun p hp => (axial_smoothAt H v upper B _ hp.1).contDiffWithinAt

theorem periodicPhase_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (g : CommonCoverSolve.Geometry) (w : PeriodicPhaseAssembly.ClockWindow)
    {p : Slow} (hp : 0 < p.2.2) (Y : TorusInverse.Plane) :
    let P := (PrimaryGeometryAssembly.construction H v a hr0 j).phase
    periodicPhase H v a hr0 j L g w (p, Y) =
      P.pz L / P.epsilon L * p.2.1 + P.x0 L * p.1 -
        PeriodicPhaseAssembly.periodicClock g w.cutoff Y * (P.p L * P.F L p + P.pz L * P.G L p) := by
  dsimp only [periodicPhase, PeriodicPhaseAssembly.phase, phase]
  rw [frequency_eq H v upper B _ hp, axial_eq H v upper B _ hp]
  rfl

noncomputable def carrier (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (g : CommonCoverSolve.Geometry) (w : PeriodicPhaseAssembly.ClockWindow) :
    Slow × TorusInverse.Plane → ℂ :=
  HarmonicCalculus.carrier (ChartScales.carrier F.data.h (BaseChartJets.cellBand L))
    (periodicPhase H v a hr0 j L g w)

theorem carrier_smooth (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (g : CommonCoverSolve.Geometry) (w : PeriodicPhaseAssembly.ClockWindow) :
    ContDiffOn ℝ ∞ (carrier H v a hr0 j L g w) (positiveStableDomain F.data.h ×ˢ univ) :=
  HarmonicCalculus.contDiffOn_carrier _ (periodicPhase_smooth H v a hr0 j L g w)

theorem carrier_eq (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    (g : CommonCoverSolve.Geometry) (w : PeriodicPhaseAssembly.ClockWindow)
    {p : Slow} (hp : 0 < p.2.2) (Y : TorusInverse.Plane) :
    let P := (PrimaryGeometryAssembly.construction H v a hr0 j).phase
    carrier H v a hr0 j L g w (p, Y) =
      HarmonicCalculus.carrier (ChartScales.carrier F.data.h (BaseChartJets.cellBand L))
        (fun z : Slow × TorusInverse.Plane => P.pz L / P.epsilon L * z.1.2.1 + P.x0 L * z.1.1 -
          PeriodicPhaseAssembly.periodicClock g w.cutoff z.2 *
            (P.p L * P.F L z.1 + P.pz L * P.G L z.1)) (p, Y) := by
  dsimp only [carrier, HarmonicCalculus.carrier]
  rw [periodicPhase_eq H v a hr0 j L g w hp Y]

theorem pulse_path_agreement (j : Fin 2) (L : PrimaryGeometryAssembly.Index W a.N)
    {p : Slow} (hp : 0 < p.2.2) :
    (fun s => pulse H v a hr0 j L (p, s)) =
      (fun s => let P := PrimaryGeometryAssembly.construction H v a hr0 j
        PrimaryPulseBounds.normalizedPulse (P.frame L) (P.lam L) (P.u L) (P.L L) (p, s)) :=
  funext (pulse_eq H v a hr0 j L hp)

end SelectedPhase

section ActualContext

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

noncomputable def stressModel (n : ℕ) (y : Model) : ℝ × ℝ :=
  (ChartScales.epsilon F.data.h n * y.1 ^ (-CoordinateAlgebra.A F.data.h - 1 / 2)) •
    FinalSlowBase.normalizedStress H v upper B
      (SlowBorelBase.scaleMap (ChartScales.Q n) (modelCoordinates F.data.h y))

noncomputable def stress (n : ℕ) : Slow → ℝ × ℝ := stressModel H v upper B n ∘ stablePoint F.data.h

noncomputable def virtualStress (n : ℕ) (p : Slow) : ℝ × ℝ :=
  if 0 < p.1 then stress H v upper B n p else 0

theorem stressModel_smoothAt (n : ℕ) {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (stressModel H v upper B n) y := by
  have hc := (SlowBorelBase.scaleMap (ChartScales.Q n)).contDiff.contDiffAt.comp y
    (modelCoordinates_smoothAt F.data.h hy)
  have hs := FinalSlowBase.normalizedStress_smoothAt H v upper B
    (y := SlowBorelBase.scaleMap (ChartScales.Q n) (modelCoordinates F.data.h y))
    (mul_pos (ChartScales.Q_pos n) hy)
  exact (contDiffAt_const.mul (contDiffAt_fst.rpow_const_of_ne hy.ne')).smul
    (ContDiffAt.comp (g := FinalSlowBase.normalizedStress H v upper B) y hs hc)

theorem stress_smoothAt (n : ℕ) {p : Slow} (hp : p ∈ stableDomain F.data.h) :
    ContDiffAt ℝ ∞ (stress H v upper B n) p :=
  (stressModel_smoothAt H v upper B n (stablePoint_pos hp)).comp p
    (stablePoint_smoothAt F.data.h_pos F.data.h_lt_half hp)

theorem stress_eq (n : ℕ) {x : LocalSignedRequest.Point} (ht : 0 < x.2.1.1) :
    stress H v upper B n (BaseContextAssembly.slowCoordinates x) =
      BaseContextAssembly.rawStress H v upper B n x := by
  rw [BaseContextAssembly.rawStress_normalized H v upper B n ht]
  change stressModel H v upper B n (stablePoint F.data.h (BaseContextAssembly.slowCoordinates x)) = _
  rw [stablePoint_eq F.data.h_pos F.data.h_lt_half ht]
  unfold stressModel
  rw [modelCoordinates_original]
  simp only [originalPoint, BaseChartJets.normalizedCoordinates_eq]

theorem virtualStress_eq (n : ℕ) {x : LocalSignedRequest.Point} (ht : 0 < x.2.1.1) :
    virtualStress H v upper B n (BaseContextAssembly.slowCoordinates x) =
      BaseContextAssembly.virtualStress H v upper B n x := by
  change (if 0 < x.1 then stress H v upper B n (BaseContextAssembly.slowCoordinates x) else 0) = _
  rw [stress_eq H v upper B n ht]
  rfl

theorem stress_zero_of_inner (n : ℕ) {p : Slow}
    (hp : (modelCoordinates F.data.h (stablePoint F.data.h p)).2.1 ≤ NominalConeAssembly.activeLeft W) :
    stress H v upper B n p = 0 := by
  change (_ : ℝ) • FinalSlowBase.normalizedStress H v upper B
    (SlowBorelBase.scaleMap (ChartScales.Q n) (modelCoordinates F.data.h (stablePoint F.data.h p))) = 0
  rw [SlowBorelBase.scaleMap_apply, FinalSlowBase.normalizedStress_zero_left H v upper B _ hp, smul_zero]

theorem virtualStress_smoothAt (n : ℕ) {p : Slow} (hp : p ∈ stableDomain F.data.h) :
    ContDiffAt ℝ ∞ (virtualStress H v upper B n) p := by
  rcases lt_trichotomy p.1 0 with hneg | hzero | hpos
  · have he : virtualStress H v upper B n =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [continuousAt_fst (gt_mem_nhds hneg)] with y hy
      change y.1 < 0 at hy
      simp only [virtualStress, ite_eq_right (not_lt.mpr hy.le)]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hc := (modelCoordinates_smoothAt F.data.h (stablePoint_pos hp)).comp p
      (stablePoint_smoothAt F.data.h_pos F.data.h_lt_half hp)
    have hx : (modelCoordinates F.data.h (stablePoint F.data.h p)).2.1 < NominalConeAssembly.activeLeft W := by
      simpa only [modelCoordinates, stablePoint, hzero, zero_pow (by decide : 2 ≠ 0), zero_div] using
        NominalConeAssembly.activeLeft_pos W
    have he : virtualStress H v upper B n =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hc.snd.fst.continuousAt (gt_mem_nhds hx)] with y hy
      change (modelCoordinates F.data.h (stablePoint F.data.h y)).2.1 < NominalConeAssembly.activeLeft W at hy
      simp only [virtualStress, stress_zero_of_inner H v upper B n hy.le, ite_self]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have he : virtualStress H v upper B n =ᶠ[𝓝 p] stress H v upper B n := by
      filter_upwards [continuousAt_fst (lt_mem_nhds hpos)] with y hy
      exact ite_eq_left hy
    exact (stress_smoothAt H v upper B n hp).congr_of_eventuallyEq he

noncomputable def context (index : ℕ → ℕ) : CorrectionState.Context LocalSignedRequest.Point :=
  { CommonBaseContext.context H v upper B index with
    base := {
      radial := fun n x => radial H v upper B n (BaseContextAssembly.slowCoordinates x)
      angular := fun n x => x.1 * frequency H v upper B n (BaseContextAssembly.slowCoordinates x)
      axial := fun n x => axial H v upper B n (BaseContextAssembly.slowCoordinates x) }
    virtualTheta := fun n x => (virtualStress H v upper B n (BaseContextAssembly.slowCoordinates x)).1
    virtualAxial := fun n x => (virtualStress H v upper B n (BaseContextAssembly.slowCoordinates x)).2 }

theorem context_operators (index : ℕ → ℕ) :
    (context H v upper B index).operators = (CommonBaseContext.context H v upper B index).operators := rfl

theorem context_base_eq (index : ℕ → ℕ) (n : ℕ) {x : LocalSignedRequest.Point} (ht : 0 < x.2.1.1) :
    (context H v upper B index).base.radial n x = (CommonBaseContext.context H v upper B index).base.radial n x ∧
    (context H v upper B index).base.angular n x = (CommonBaseContext.context H v upper B index).base.angular n x ∧
    (context H v upper B index).base.axial n x = (CommonBaseContext.context H v upper B index).base.axial n x := by
  refine ⟨?_, ?_, ?_⟩
  · exact radial_eq H v upper B n ht
  · exact congrArg (fun r => x.1 * r) (frequency_eq H v upper B n ht)
  · exact axial_eq H v upper B n ht

theorem context_stress_eq (index : ℕ → ℕ) (n : ℕ) {x : LocalSignedRequest.Point} (ht : 0 < x.2.1.1) :
    (context H v upper B index).virtualTheta n x = (CommonBaseContext.context H v upper B index).virtualTheta n x ∧
    (context H v upper B index).virtualAxial n x = (CommonBaseContext.context H v upper B index).virtualAxial n x :=
  ⟨congrArg Prod.fst (virtualStress_eq H v upper B n ht), congrArg Prod.snd (virtualStress_eq H v upper B n ht)⟩

noncomputable def contextDomain (h : ℝ) : Set LocalSignedRequest.Point :=
  BaseContextAssembly.slowCoordinates ⁻¹' positiveStableDomain h

theorem contextDomain_open (h : ℝ) : IsOpen (contextDomain h) :=
  (positiveStableDomain_open h).preimage BaseContextAssembly.slowCoordinates.continuous

theorem contextDomain_endpoint (R : ℝ) (hR : 0 < R) {Z : ℝ} (hZ : Z ≠ 0) (Y : TorusInverse.Plane) :
    (R, ((0, Z), Y)) ∈ contextDomain F.data.h :=
  ⟨endpoint_mem_stable F.data.h_pos F.data.h_lt_half R hZ, hR⟩

theorem context_base_smooth (index : ℕ → ℕ) :
    MeanIncrementBounds.SmoothTriple (contextDomain F.data.h) (context H v upper B index).base := by
  refine ⟨fun n x hx => ?_, fun n x hx => ?_, fun n x hx => ?_⟩
  · exact ((radial_smoothAt H v upper B n hx.1).comp x
      BaseContextAssembly.slowCoordinates.contDiff.contDiffAt).contDiffWithinAt
  · exact (contDiffAt_fst.mul ((frequency_smoothAt H v upper B n hx).comp x
      BaseContextAssembly.slowCoordinates.contDiff.contDiffAt)).contDiffWithinAt
  · exact ((axial_smoothAt H v upper B n hx.1).comp x
      BaseContextAssembly.slowCoordinates.contDiff.contDiffAt).contDiffWithinAt

theorem context_stress_smooth (index : ℕ → ℕ) (n : ℕ) :
    ContDiffOn ℝ ∞ ((context H v upper B index).virtualTheta n) (contextDomain F.data.h) ∧
    ContDiffOn ℝ ∞ ((context H v upper B index).virtualAxial n) (contextDomain F.data.h) := by
  constructor
  · intro x hx
    exact (((virtualStress_smoothAt H v upper B n hx.1).comp x
      BaseContextAssembly.slowCoordinates.contDiff.contDiffAt).fst).contDiffWithinAt
  · intro x hx
    exact (((virtualStress_smoothAt H v upper B n hx.1).comp x
      BaseContextAssembly.slowCoordinates.contDiff.contDiffAt).snd).contDiffWithinAt

theorem context_base_germ (index : ℕ → ℕ) (n : ℕ) {x : LocalSignedRequest.Point} (ht : 0 < x.2.1.1) :
    HarmonicResidual.contextBase (context H v upper B index) n =ᶠ[𝓝 x]
      HarmonicResidual.contextBase (CommonBaseContext.context H v upper B index) n := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd.fst.fst).mem_nhds ht] with y hy
  have he := context_base_eq H v upper B index n hy
  simp only [HarmonicResidual.contextBase, he.1, he.2.1, he.2.2]

/-- Equality is on every free radial/torus fiber, not only a graph restriction. -/
theorem context_stress_fiberAgreement (index : ℕ → ℕ) (n : ℕ) (U : Set TorusInverse.Plane) :
    OffplaneCorrectionExtensions.FiberAgreement U ((context H v upper B index).virtualTheta n)
      ((CommonBaseContext.context H v upper B index).virtualTheta n) ∧
    OffplaneCorrectionExtensions.FiberAgreement U ((context H v upper B index).virtualAxial n)
      ((CommonBaseContext.context H v upper B index).virtualAxial n) :=
  ⟨fun _ hx => (context_stress_eq H v upper B index n hx.2).1,
    fun _ hx => (context_stress_eq H v upper B index n hx.2).2⟩

theorem context_base_fiberAgreement (index : ℕ → ℕ) (n : ℕ) (U : Set TorusInverse.Plane) :
    OffplaneCorrectionExtensions.FiberAgreement U ((context H v upper B index).base.radial n)
      ((CommonBaseContext.context H v upper B index).base.radial n) ∧
    OffplaneCorrectionExtensions.FiberAgreement U ((context H v upper B index).base.angular n)
      ((CommonBaseContext.context H v upper B index).base.angular n) ∧
    OffplaneCorrectionExtensions.FiberAgreement U ((context H v upper B index).base.axial n)
      ((CommonBaseContext.context H v upper B index).base.axial n) :=
  ⟨fun _ hx => (context_base_eq H v upper B index n hx.2).1,
    fun _ hx => (context_base_eq H v upper B index n hx.2).2.1,
    fun _ hx => (context_base_eq H v upper B index n hx.2).2.2⟩

end ActualContext

section DifferentialPreservation

open OffplaneCorrectionExtensions MeanIncrementBounds

/-- Agreement through actual graph differentiation, with the free radial
and torus coordinates retained.  These are the differential operations used
in the particular and mean residual formulas. -/
theorem fiberAgreement_dr {U : Set TorusInverse.Plane} (hU : IsOpen U)
    (o : Operators LocalSignedRequest.Point) {F f : MeanIncrementBounds.Field LocalSignedRequest.Point}
    (h : ∀ n, FiberAgreement U (F n) (f n)) :
    ∀ n, FiberAgreement U (o.dr F n) (o.dr f n) :=
  Operators.dr_congr (PhysicalMeanDomain.slowDomain_open (hU.inter positiveSlow_open)) o h

theorem fiberAgreement_dz {U : Set TorusInverse.Plane} (hU : IsOpen U)
    (o : Operators LocalSignedRequest.Point) {F f : MeanIncrementBounds.Field LocalSignedRequest.Point}
    (h : ∀ n, FiberAgreement U (F n) (f n)) :
    ∀ n, FiberAgreement U (o.dz F n) (o.dz f n) :=
  Operators.dz_congr (PhysicalMeanDomain.slowDomain_open (hU.inter positiveSlow_open)) o h

theorem fiberAgreement_time {U : Set TorusInverse.Plane} (hU : IsOpen U)
    (o : Operators LocalSignedRequest.Point) {F f : MeanIncrementBounds.Field LocalSignedRequest.Point}
    (h : ∀ n, FiberAgreement U (F n) (f n)) :
    ∀ n, FiberAgreement U (o.time F n) (o.time f n) := by
  intro n x hx
  have he := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) ((h n).eventuallyEq hU hx.1 hx.2)
  simp only [Operators.time, Operators.slowTime, Operators.fastTime, Pi.add_apply, he]

theorem fiberAgreement_viscosity {U : Set TorusInverse.Plane} (hU : IsOpen U)
    (o : Operators LocalSignedRequest.Point) (c : ℝ) {F f : MeanIncrementBounds.Field LocalSignedRequest.Point}
    (h : ∀ n, FiberAgreement U (F n) (f n)) :
    ∀ n, FiberAgreement U (o.viscosity c F n) (o.viscosity c f n) := by
  have hr := fiberAgreement_dr hU o h
  have hrr := fiberAgreement_dr hU o hr
  have hzz := fiberAgreement_dz hU o (fiberAgreement_dz hU o h)
  intro n x hx
  simp only [Operators.viscosity, hrr n hx, hr n hx, hzz n hx, h n hx]

theorem fiberAgreement_mul {U : Set TorusInverse.Plane} {F f G g : LocalSignedRequest.Point → ℝ}
    (hF : FiberAgreement U F f) (hG : FiberAgreement U G g) :
    FiberAgreement U (fun x => F x * G x) (fun x => f x * g x) :=
  fun _ hx => congrArg₂ (· * ·) (hF hx) (hG hx)

theorem fiberAgreement_add {U : Set TorusInverse.Plane} {F f G g : LocalSignedRequest.Point → ℝ}
    (hF : FiberAgreement U F f) (hG : FiberAgreement U G g) :
    FiberAgreement U (fun x => F x + G x) (fun x => f x + g x) :=
  fun _ hx => congrArg₂ (· + ·) (hF hx) (hG hx)

end DifferentialPreservation

end NavierStokes.ActualCorrectionModels
