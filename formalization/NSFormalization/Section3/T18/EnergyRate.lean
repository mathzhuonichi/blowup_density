import NSFormalization.Section3.T18.Divergence
import Mathlib.Topology.Semicontinuity.Basic

/-!
# T18 U9: the energy closeness estimate

The analytic part of `eq:Eclose` is the triangle inequality for the torus
energy functional.  The `L^infty_t L^2_x` half follows from `essSup_add_le`;
the gradient half is Minkowski in `ℝ≥0∞` at exponent two.  Measurability of
the time-dependent spatial gradient norm is obtained from slab smoothness by
Fatou's lemma on the open-time subtype.
-/

noncomputable section

namespace NSFormalization.Section3.T18

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.I02 (spatialGradient)
open NavierStokes.PeriodicIntegration (Coords toSpace)
open scoped ContDiff ENNReal Topology

/-- The canonical `(0,1]³` representative used definitionally by
`torusLift`. -/
def energyTorusChart (z : PeriodicTorus) : Space :=
  toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val)

/-- Spatial differentiation preserves slab smoothness. -/
theorem contDiffOn_spatialFDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set ℝ} {F : SpaceTime → E}
    (hF : ContDiffOn ℝ ∞ F (s ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime => fderiv ℝ (fun x => F (z.1, x)) z.2)
      (s ×ˢ (univ : Set Space)) := by
  intro z hz
  have h : ContDiffOn ℝ ∞
      (fun p : SpaceTime × Space => F (p.1.1, p.2))
      ((s ×ˢ (univ : Set Space)) ×ˢ (univ : Set Space)) :=
    hF.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  simpa only [fderivWithin_univ] using
    (h (z, z.2) ⟨hz, mem_univ _⟩).fderivWithin
      contDiffWithinAt_snd uniqueDiffOn_univ (by simp) hz (fun _ _ => mem_univ _)

/-- Spatial gradients commute with addition at every point where both spatial
slices are differentiable. -/
theorem spatialGradient_add {u v : SpaceTimeField} {t : ℝ} (x : Space)
    (hu : DifferentiableAt ℝ (fun y : Space => u (t, y)) x)
    (hv : DifferentiableAt ℝ (fun y : Space => v (t, y)) x) :
    spatialGradient (fun z => u z + v z) t x =
      spatialGradient u t x + spatialGradient v t x := by
  have hd := fderiv_add hu hv
  apply PiLp.ext
  intro i
  exact congrFun (congrArg DFunLike.coe hd) (coordinateVector i)

/-- On an open time slab, the spatial `L^2` norm of the full gradient is
measurable for the restricted time measure.  The per-slice `MemLp` hypothesis
is exactly the honesty guard carried by the T15 and T17 records. -/
theorem gradientSliceNorm_aemeasurable {T : ℝ} {u : SpaceTimeField}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hmem : ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x => spatialGradient u t x)) 2 periodicTorusMeasure) :
    AEMeasurable
      (fun t => eLpNorm (torusLift (fun x => spatialGradient u t x)) 2
        periodicTorusMeasure)
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  apply aemeasurable_restrict_of_measurable_subtype measurableSet_Ioo
  have hcontinuous (z : PeriodicTorus) : Continuous fun t : Ioo (0 : ℝ) T =>
      spatialGradient u t.1 (energyTorusChart z) := by
    have hfd : Continuous fun t : Ioo (0 : ℝ) T =>
        fderiv ℝ (fun x : Space => u (t.1, x)) (energyTorusChart z) := by
      exact (contDiffOn_spatialFDeriv hu).continuousOn.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun t : Ioo (0 : ℝ) T => ⟨⟨t.2.1.le, t.2.2⟩, mem_univ _⟩)
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Space)).comp
      (continuous_pi fun i => hfd.clm_apply continuous_const)
  have hlsc : LowerSemicontinuous fun t : Ioo (0 : ℝ) T =>
      eLpNorm (torusLift (fun x => spatialGradient u t.1 x)) 2
        periodicTorusMeasure := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro C
    apply IsSeqClosed.isClosed
    intro ts t hC ht
    apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
      (f := fun n z => torusLift (fun x => spatialGradient u (ts n).1 x) z)
      (Eventually.of_forall hC)
      (fun n => (hmem (ts n).1 (ts n).2).aestronglyMeasurable)
    apply Eventually.of_forall
    intro z
    exact ((hcontinuous z).tendsto t).comp ht
  exact hlsc.measurable

/-- The `L^infty_t L^2_x` half of the torus energy functional is subadditive. -/
theorem energyEssSupT_add_le {T : ℝ} {u v : SpaceTimeField}
    (hu : ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x => u (t, x))) 2 periodicTorusMeasure)
    (hv : ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x => v (t, x))) 2 periodicTorusMeasure) :
    energyEssSupT T (fun z => u z + v z) ≤
      energyEssSupT T u + energyEssSupT T v := by
  unfold energyEssSupT
  calc
    essSup (fun t => eLpNorm (torusLift (fun x => u (t, x) + v (t, x))) 2
        periodicTorusMeasure) (volume.restrict (Ioo (0 : ℝ) T))
      ≤ essSup (fun t =>
          eLpNorm (torusLift (fun x => u (t, x))) 2 periodicTorusMeasure +
          eLpNorm (torusLift (fun x => v (t, x))) 2 periodicTorusMeasure)
          (volume.restrict (Ioo (0 : ℝ) T)) := by
        apply essSup_mono_ae (hf := by isBoundedDefault) (hg := by isBoundedDefault)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact eLpNorm_add_le (hu t ht).aestronglyMeasurable
          (hv t ht).aestronglyMeasurable (by norm_num)
    _ ≤ essSup (fun t => eLpNorm (torusLift (fun x => u (t, x))) 2
          periodicTorusMeasure) (volume.restrict (Ioo (0 : ℝ) T)) +
        essSup (fun t => eLpNorm (torusLift (fun x => v (t, x))) 2
          periodicTorusMeasure) (volume.restrict (Ioo (0 : ℝ) T)) :=
      ENNReal.essSup_add_le _ _

/-- The `L^2_t L^2_x` full-gradient half of the torus energy functional is
subadditive. -/
theorem energyGradientT_add_le {T : ℝ} {u v : SpaceTimeField}
    (hus : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hvs : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hu : ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x => spatialGradient u t x)) 2 periodicTorusMeasure)
    (hv : ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x => spatialGradient v t x)) 2 periodicTorusMeasure) :
    energyGradientT T (fun z => u z + v z) ≤
      energyGradientT T u + energyGradientT T v := by
  let A : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (torusLift (fun x => spatialGradient u t x)) 2 periodicTorusMeasure
  let B : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (torusLift (fun x => spatialGradient v t x)) 2 periodicTorusMeasure
  have hA : AEMeasurable A (volume.restrict (Ioo (0 : ℝ) T)) :=
    gradientSliceNorm_aemeasurable hus hu
  have hB : AEMeasurable B (volume.restrict (Ioo (0 : ℝ) T)) :=
    gradientSliceNorm_aemeasurable hvs hv
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) T,
      eLpNorm (torusLift (fun x => spatialGradient (fun z => u z + v z) t x)) 2
          periodicTorusMeasure ≤ A t + B t := by
    intro t ht
    have hdiffu (x : Space) := spatial_slice_differentiable hus
      ⟨ht.1.le, ht.2⟩ x
    have hdiffv (x : Space) := spatial_slice_differentiable hvs
      ⟨ht.1.le, ht.2⟩ x
    have heq : (fun x => spatialGradient (fun z => u z + v z) t x) =
        (fun x => spatialGradient u t x + spatialGradient v t x) := by
      funext x
      exact spatialGradient_add x (hdiffu x) (hdiffv x)
    rw [heq]
    exact eLpNorm_add_le (hu t ht).aestronglyMeasurable
      (hv t ht).aestronglyMeasurable (by norm_num)
  unfold energyGradientT
  change (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (torusLift (fun x => spatialGradient (fun z => u z + v z) t x)) 2
        periodicTorusMeasure) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤ _
  calc
    (∫⁻ t in Ioo (0 : ℝ) T,
        (eLpNorm (torusLift (fun x => spatialGradient (fun z => u z + v z) t x)) 2
          periodicTorusMeasure) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)
      ≤ (∫⁻ t in Ioo (0 : ℝ) T, (A t + B t) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact ENNReal.rpow_le_rpow (hpoint t ht) (by norm_num)
    _ ≤ (∫⁻ t in Ioo (0 : ℝ) T, A t ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) +
        (∫⁻ t in Ioo (0 : ℝ) T, B t ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
      simpa only [Pi.add_apply, one_div] using
        (ENNReal.lintegral_Lp_add_le hA hB (by norm_num : (1 : ℝ) ≤ 2))

/-- Triangle inequality for the full torus energy functional. -/
theorem energyENormT_add_le {T : ℝ} {u v : SpaceTimeField}
    (hus : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hvs : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hu : EnergySlicesMemLpT T u) (hv : EnergySlicesMemLpT T v) :
    energyENormT T (fun z => u z + v z) ≤ energyENormT T u + energyENormT T v := by
  unfold energyENormT
  exact add_le_add (energyEssSupT_add_le hu.1 hv.1)
    (energyGradientT_add_le hus hvs hu.2 hv.2) |>.trans_eq (by ac_rfl)

/-- The inserted velocity difference is the correction plus the packet. -/
theorem velocityDifference_eq_correction_add_packet (data : InsertionData) (ε : ℝ) :
    (fun z => velocity data ε z - data.reference.velocity z) =
      fun z => data.D.correction ε z +
        periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε z := by
  funext z
  simp only [velocity]
  abel

/-- The energy norm of the inserted difference is at most the sum of the two
threaded energy norms. -/
theorem velocityDifference_energyENorm_le (data : InsertionData) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) :
    energyENormT data.place.T
        (fun z => velocity data ε z - data.reference.velocity z) ≤
      energyENormT data.place.T (data.D.correction ε) +
        energyENormT data.place.T
          (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε) := by
  rw [velocityDifference_eq_correction_add_packet]
  obtain ⟨S, hSU, _⟩ := data.scaling.solution ε (scaling_range data hε)
  apply energyENormT_add_le
  · exact (data.correction.potential.correction_smooth ε
      (correction_range data hε)).contDiffOn
  · simpa only [hSU] using S.velocity_smooth
  · exact ⟨fun t _ => data.correction.correction_slice_memLp ε
      (correction_range data hε) t,
      fun t _ => data.correction.correction_gradient_memLp ε
        (correction_range data hε) t⟩
  · exact data.scaling.energySlices_memLp ε (scaling_range data hε)

/-- The packet's full energy norm is the sum of its two exact scaling
identities. -/
theorem packet_energyENorm_eq (data : InsertionData) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) :
    energyENormT data.place.T
        (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.energyBound) +
        ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.dissipationBound) := by
  unfold energyENormT
  rw [data.scaling.packetEnergyIdentity ε (scaling_range data hε),
    data.scaling.packetDissipationIdentity ε (scaling_range data hε)]

private theorem add_rotate (a b c : ℝ≥0∞) : c + (a + b) = a + b + c := by
  ac_rfl

/-- The analytic and record-bookkeeping part of `eq:Eclose`, leaving the two
raw packet constants as separate `ENNReal.ofReal` terms. -/
theorem energyRate_separateConstants (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      energyENormT data.place.T
          (fun z => velocity data ε z - data.reference.velocity z) ≤
        ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.energyBound) +
          ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.dissipationBound) +
          ENNReal.ofReal
            (data.correction.energyConst * ε ^ ((3 : ℝ) / 2)) := by
  intro ε hε
  have hmain := velocityDifference_energyENorm_le data hε
  rw [packet_energyENorm_eq data hε] at hmain
  have hcorr := data.correction.correction_energy_bound ε (correction_range data hε)
  calc
    energyENormT data.place.T
        (fun z => velocity data ε z - data.reference.velocity z)
      ≤ energyENormT data.place.T (data.D.correction ε) +
          (ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.energyBound) +
            ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.dissipationBound)) := hmain
    _ ≤ ENNReal.ofReal
          (data.correction.energyConst * ε ^ ((3 : ℝ) / 2)) +
        (ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.energyBound) +
          ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.dissipationBound)) :=
      add_le_add_left hcorr _
    _ = _ := add_rotate _ _ _

end NSFormalization.Section3.T18
