import NSFormalization.Section3.T18.Insertion
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section3.T11.Persistence
import NSFormalization.Paper1.ScalingLimits

/-!
# T18 U11: Sobolev rate for the inserted force

This module combines the packet and correction `L¹_t H^s_x` estimates carried
by the threaded T15 and T17 records.  It also proves, directly from the
infimum-over-paths definition, the two structural facts needed here: the
triangle inequality and monotonicity under lowering the Sobolev order.
-/

noncomputable section

namespace NSFormalization.Section3.T18

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open scoped ENNReal Topology BigOperators

/-! ## Path algebra and order lowering -/

/-- Fourier coefficients commute with addition for integrable torus lifts. -/
theorem periodicFourierCoeff_add_integrable {f g : Space → ℂ}
    (hf : Integrable (torusLift f) periodicTorusMeasure)
    (hg : Integrable (torusLift g) periodicTorusMeasure)
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x + g x) k =
      periodicFourierCoeff f k + periodicFourierCoeff g k := by
  change Integrable (torusLift f)
    (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) at hf
  change Integrable (torusLift g)
    (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) at hg
  change UnitAddTorus.mFourierCoeff
      (fun y : PeriodicTorus ↦ torusLift f y + torusLift g y) k =
    UnitAddTorus.mFourierCoeff (torusLift f) k +
      UnitAddTorus.mFourierCoeff (torusLift g) k
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_add]
  rw [integral_add]
  · unfold MeasureTheory.MeasureSpace.pi
    have hm : AEStronglyMeasurable
        (fun x : PeriodicTorus ↦ UnitAddTorus.mFourier (-k) x)
        periodicTorusMeasure :=
      (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
    have hb : ∀ᵐ x : PeriodicTorus ∂periodicTorusMeasure,
        ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
      filter_upwards with x
      simpa only [UnitAddTorus.mFourier_norm] using
        (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x
    convert hf.bdd_smul (φ := fun x ↦ UnitAddTorus.mFourier (-k) x) 1 hm hb using 1 <;>
      rfl
  · unfold MeasureTheory.MeasureSpace.pi
    have hm : AEStronglyMeasurable
        (fun x : PeriodicTorus ↦ UnitAddTorus.mFourier (-k) x)
        periodicTorusMeasure :=
      (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
    have hb : ∀ᵐ x : PeriodicTorus ∂periodicTorusMeasure,
        ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
      filter_upwards with x
      simpa only [UnitAddTorus.mFourier_norm] using
        (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x
    convert hg.bdd_smul (φ := fun x ↦ UnitAddTorus.mFourier (-k) x) 1 hm hb using 1 <;>
      rfl

/-- Fourier data are additive jointly with their physical realizations. -/
theorem periodicDatum_add {s : ℝ} {v w : SpatialField}
    {A B : PeriodicSobolev s} (hA : IsPeriodicDatum s v A)
    (hB : IsPeriodicDatum s w B) :
    IsPeriodicDatum s (fun x ↦ v x + w x) (A + B) := by
  refine ⟨fun x j ↦ by simp only [hA.1 x j, hB.1 x j],
    hA.2.1.add hB.2.1, ?_⟩
  intro i k
  change A.1 i k + B.1 i k = _
  rw [hA.2.2, hB.2.2, ← smul_add]
  congr 1
  simpa only [Pi.add_apply, PiLp.add_apply, Complex.ofReal_add] using
    (periodicFourierCoeff_add_integrable
      (hA.integrable_component i) (hB.integrable_component i) k).symm

/-- The sum of two honest Sobolev force paths is an honest path for the
pointwise sum. -/
theorem memForceSobolevT_add {q : ℝ≥0∞} {s : ℝ} {f g : SpaceTimeField}
    (hf : MemForceSobolevT q s f) (hg : MemForceSobolevT q s g) :
    MemForceSobolevT q s (fun z ↦ f z + g z) := by
  obtain ⟨F, hF, hFLp⟩ := hf
  obtain ⟨G, hG, hGLp⟩ := hg
  refine ⟨fun t ↦ F t + G t, ?_, hFLp.add hGLp⟩
  intro t ht
  exact periodicDatum_add (hF t ht) (hG t ht)

/-- Uniqueness of the datum of each nonnegative-time slice evaluates the
path infimum at every admissible path. -/
theorem forceSobolevENormT_eq_of_path_local (q : ℝ≥0∞) (s : ℝ)
    {f : SpaceTimeField} {G : ℝ → PeriodicSobolev s}
    (hG : IsPeriodicSobolevPath s f G)
    (hm : AEStronglyMeasurable G forceTimeMeasure) :
    forceSobolevENormT q s f = eLpNorm G q forceTimeMeasure := by
  refine le_antisymm (iInf_le_of_le ⟨G, hG, hm⟩ le_rfl) (le_iInf ?_)
  rintro ⟨G', hG', -⟩
  have hae : G' =ᵐ[forceTimeMeasure] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact datum_unique s (fun x ↦ f (t, x)) (G' t) (G t)
      (hG' t (le_of_lt ht)) (hG t (le_of_lt ht))
  exact le_of_eq (eLpNorm_congr_ae hae).symm

/-- Minkowski for the registered infimum-over-Sobolev-paths force norm. -/
theorem forceSobolevENormT_add_le {q : ℝ≥0∞} {s : ℝ}
    (hq : 1 ≤ q) {f g : SpaceTimeField}
    (hf : MemForceSobolevT q s f) (hg : MemForceSobolevT q s g) :
    forceSobolevENormT q s (fun z ↦ f z + g z) ≤
      forceSobolevENormT q s f + forceSobolevENormT q s g := by
  obtain ⟨F, hF, hFLp⟩ := hf
  obtain ⟨G, hG, hGLp⟩ := hg
  have hsum : IsPeriodicSobolevPath s (fun z ↦ f z + g z)
      (fun t ↦ F t + G t) := by
    intro t ht
    exact periodicDatum_add (hF t ht) (hG t ht)
  calc
    forceSobolevENormT q s (fun z ↦ f z + g z) =
        eLpNorm (fun t ↦ F t + G t) q forceTimeMeasure :=
      forceSobolevENormT_eq_of_path_local q s hsum
        (hFLp.1.add hGLp.1)
    _ ≤ eLpNorm F q forceTimeMeasure + eLpNorm G q forceTimeMeasure :=
      eLpNorm_add_le hFLp.1 hGLp.1 hq
    _ = forceSobolevENormT q s f + forceSobolevENormT q s g := by
      rw [forceSobolevENormT_eq_of_path_local q s hF hFLp.1,
        forceSobolevENormT_eq_of_path_local q s hG hGLp.1]

/-- T11's Bessel-weight lowering map is contractive. -/
theorem persistenceDown_norm_le (t s : ℝ) (hst : s ≤ t)
    (A : PeriodicSobolev t) : ‖persistenceDown t s hst A‖ ≤ ‖A‖ := by
  change ‖torusMultiplier t s (fun k ↦ periodicFrequencyWeight k ^ ((s - t) / 2))
      1 zero_le_one (persistence_down_weight_le hst)
      (fun k ↦ by rw [torus_weight_neg]) A‖ ≤ ‖A‖
  simpa only [one_mul] using
    torusMultiplier_norm_le t s
      (fun k ↦ periodicFrequencyWeight k ^ ((s - t) / 2))
      1 zero_le_one (persistence_down_weight_le hst)
      (fun k ↦ by rw [torus_weight_neg]) A

/-- The registered force norm decreases when the Sobolev order is lowered. -/
theorem forceSobolevENormT_mono_order (q : ℝ≥0∞) {s t : ℝ}
    (hst : s ≤ t) (f : SpaceTimeField) :
    forceSobolevENormT q s f ≤ forceSobolevENormT q t f := by
  refine le_iInf fun G ↦ ?_
  let L := persistenceDown t s hst
  have hpath : IsPeriodicSobolevPath s f (fun r ↦ L (G.1 r)) := by
    intro r hr
    exact persistence_datum_of_reweight (G.2.1 r hr)
      (persistenceDown_reweight t s hst (G.1 r))
  have hmeas : AEStronglyMeasurable (fun r ↦ L (G.1 r)) forceTimeMeasure :=
    L.continuous.comp_aestronglyMeasurable G.2.2
  calc
    forceSobolevENormT q s f ≤ eLpNorm (fun r ↦ L (G.1 r)) q forceTimeMeasure :=
      iInf_le (fun H : {H : ℝ → PeriodicSobolev s //
        IsPeriodicSobolevPath s f H ∧ AEStronglyMeasurable H forceTimeMeasure} ↦
          eLpNorm H.1 q forceTimeMeasure) ⟨_, hpath, hmeas⟩
    _ ≤ eLpNorm G.1 q forceTimeMeasure :=
      eLpNorm_mono (fun r ↦ persistenceDown_norm_le t s hst (G.1 r))

/-- An honest path at a higher order lowers to an honest path at every lower
order. -/
theorem memForceSobolevT_mono_order {q : ℝ≥0∞} {s t : ℝ}
    (hst : s ≤ t) {f : SpaceTimeField} (hf : MemForceSobolevT q t f) :
    MemForceSobolevT q s f := by
  obtain ⟨G, hG, hGLp⟩ := hf
  let L := persistenceDown t s hst
  refine ⟨fun r ↦ L (G r), ?_, hGLp.continuousLinearMap_comp L⟩
  intro r hr
  exact persistence_datum_of_reweight (hG r hr)
    (persistenceDown_reweight t s hst (G r))

/-! ## The inserted force difference -/

/-- The reference force cancels, leaving the correction force plus the
periodized packet force. -/
theorem force_difference_eq (data : InsertionData) (ε : ℝ) :
    (fun z ↦ force data ε z - data.g z) =
      fun z ↦ correctionForce data.ν data.reference.velocity data.D ε z +
        periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z := by
  funext z
  simp only [force]
  abel

/-- The rate constant absorbs the two lower-order summands in the threaded
packet and correction estimates. -/
def forceDiffSobolevConst (data : InsertionData) (s : ℝ) : ℝ :=
  2 * (data.scaling.sobolevConst s + data.correction.sobolevConst s)

/-- The selected rate constant is strictly positive throughout the range used
by `eq:Hsclose`. -/
theorem forceDiffSobolevConst_pos (data : InsertionData) :
    ∀ s : ℝ, 0 ≤ s → s < 1 / 2 → 0 < forceDiffSobolevConst data s := by
  intro s hs hsHalf
  have hs1 : s ≤ 1 := by linarith
  unfold forceDiffSobolevConst
  exact mul_pos zero_lt_two
    (add_pos (data.scaling.sobolevConst_pos s hs hs1)
      (data.correction.sobolevConst_pos s hs hs1))

/-- The actual force difference has an honest `L¹_t H^s_x` path on the
positive-order range. -/
theorem forceDifference_sobolev_memLp (data : InsertionData) :
    ∀ s : ℝ, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      MemForceSobolevT 1 s (fun z ↦ force data ε z - data.g z) := by
  intro s hs hsHalf ε hε
  have hs1 : s ≤ 1 := by linarith
  have hscale : ε ∈ Ioc (0 : ℝ) data.place.ε₀ :=
    ⟨hε.1, hε.2.trans (eps_le_scaling data)⟩
  have hcutoff : ε ∈ Ioc (0 : ℝ) data.D.ε₀ :=
    ⟨hε.1, hε.2.trans (eps_le_cutoff data)⟩
  rw [force_difference_eq]
  exact memForceSobolevT_add
    (data.correction.forceSobolev_memLp s hs hs1 ε hcutoff)
    (data.scaling.forceSobolev_memLp s hs hs1 ε hscale)

/-- `eq:Hsclose`: the inserted force differs from the reference by the stated
subcritical `L¹_t H^s_x` rate. -/
theorem forceDifference_sobolev_bound (data : InsertionData) :
    ∀ s : ℝ, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      forceSobolevENormT 1 s (fun z ↦ force data ε z - data.g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst data s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) := by
  intro s hs hsHalf ε hε
  have hs1 : s ≤ 1 := by linarith
  have hscale : ε ∈ Ioc (0 : ℝ) data.place.ε₀ :=
    ⟨hε.1, hε.2.trans (eps_le_scaling data)⟩
  have hcutoff : ε ∈ Ioc (0 : ℝ) data.D.ε₀ :=
    ⟨hε.1, hε.2.trans (eps_le_cutoff data)⟩
  have hε1 : ε ≤ 1 := hscale.2.trans data.place.eps_le_one
  have hpacketPath := data.scaling.forceSobolev_memLp s hs hs1 ε hscale
  have hcorrectionPath := data.correction.forceSobolev_memLp s hs hs1 ε hcutoff
  have hpacket := data.scaling.packetSobolevBound s hs hs1 ε hscale
  have hcorrection := data.correction.force_sobolev_bound s hs hs1 ε hcutoff
  have hpLow : ε ^ ((1 : ℝ) / 2) ≤ ε ^ ((1 : ℝ) / 2 - s) :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε1 (by linarith)
  have hcLow : ε ^ ((3 : ℝ) / 2) ≤ ε ^ ((3 : ℝ) / 2 - s) :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε1 (by linarith)
  have hscaleC : 0 ≤ data.scaling.sobolevConst s :=
    (data.scaling.sobolevConst_pos s hs hs1).le
  have hcorrectionC : 0 ≤ data.correction.sobolevConst s :=
    (data.correction.sobolevConst_pos s hs hs1).le
  have hpacketReal :
      0 ≤ data.scaling.sobolevConst s *
        (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)) :=
    mul_nonneg hscaleC
      (add_nonneg (Real.rpow_nonneg hε.1.le _) (Real.rpow_nonneg hε.1.le _))
  have hcorrectionReal :
      0 ≤ data.correction.sobolevConst s *
        (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)) :=
    mul_nonneg hcorrectionC
      (add_nonneg (Real.rpow_nonneg hε.1.le _) (Real.rpow_nonneg hε.1.le _))
  have hreal :
      data.correction.sobolevConst s *
          (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)) +
        data.scaling.sobolevConst s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)) ≤
        forceDiffSobolevConst data s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)) := by
    unfold forceDiffSobolevConst
    nlinarith [Real.rpow_nonneg hε.1.le ((1 : ℝ) / 2 - s),
      Real.rpow_nonneg hε.1.le ((3 : ℝ) / 2 - s)]
  rw [force_difference_eq]
  calc
    forceSobolevENormT 1 s
          (fun z ↦ correctionForce data.ν data.reference.velocity data.D ε z +
            periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z) ≤
        forceSobolevENormT 1 s
            (correctionForce data.ν data.reference.velocity data.D ε) +
          forceSobolevENormT 1 s
            (periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε) :=
      forceSobolevENormT_add_le (by norm_num) hcorrectionPath hpacketPath
    _ ≤ ENNReal.ofReal
          (data.correction.sobolevConst s *
            (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) +
        ENNReal.ofReal
          (data.scaling.sobolevConst s *
            (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))) :=
      add_le_add hcorrection hpacket
    _ = ENNReal.ofReal
        (data.correction.sobolevConst s *
            (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)) +
          data.scaling.sobolevConst s *
            (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))) := by
      rw [ENNReal.ofReal_add hcorrectionReal hpacketReal]
    _ ≤ ENNReal.ofReal (forceDiffSobolevConst data s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) :=
      ENNReal.ofReal_le_ofReal hreal

/-! ## The negative-order tail -/

/-- The `s < 0` norm is bounded by the already-controlled order-zero norm,
and therefore tends to zero with the scale. -/
theorem forceDifference_negativeSobolev_tendsto (data : InsertionData) :
    ∀ s : ℝ, s < 0 →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT 1 s
          (fun z ↦ force data ε z - data.g z))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞)) := by
  intro s hs
  have hupper : Tendsto
      (fun ε : ℝ ↦ ENNReal.ofReal (forceDiffSobolevConst data 0 *
        (ε ^ ((1 : ℝ) / 2 - 0) + ε ^ ((3 : ℝ) / 2 - 0))))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞)) := by
    have hr : Tendsto
        (fun ε : ℝ ↦ forceDiffSobolevConst data 0 *
          (ε ^ ((1 : ℝ) / 2 - 0) + ε ^ ((3 : ℝ) / 2 - 0)))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ)) := by
      simpa only using
        (NSFormalization.Paper1.sobolev_error_tendsto_zero
          0 (forceDiffSobolevConst data 0) (by norm_num)).mono_left
            nhdsWithin_le_nhds
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun _ ↦ bot_le)
  · filter_upwards [Ioc_mem_nhdsGT (eps_pos data)] with ε hε
    exact (forceSobolevENormT_mono_order 1 (le_of_lt hs)
      (fun z ↦ force data ε z - data.g z)).trans
        (forceDifference_sobolev_bound data 0 (by norm_num) (by norm_num) ε hε)

/-- The negative-order limit is backed by an actual `L¹_t H^s_x` path,
obtained by lowering the honest order-zero path. -/
theorem negative_s_memLp (data : InsertionData) :
    ∀ s : ℝ, s < 0 → ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      MemForceSobolevT 1 s (fun z ↦ force data ε z - data.g z) := by
  intro s hs ε hε
  exact memForceSobolevT_mono_order (le_of_lt hs)
    (forceDifference_sobolev_memLp data 0 (by norm_num) (by norm_num) ε hε)

end NSFormalization.Section3.T18
