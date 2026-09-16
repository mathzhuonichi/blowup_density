import Bindings.ScalingHomogeneous
import Bindings.Thresholds

noncomputable section
namespace BlowupDensity.Bindings
open Set Filter MeasureTheory
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4
open scoped ENNReal Topology ContDiff

/-- A positive power majorant vanishes at the insertion endpoint. -/
theorem grid_power_limit (K b : ℝ) (hb : 0 < b) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε ^ b)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun ε : ℝ => ENNReal.ofReal (K * ε ^ b)) := ENNReal.continuous_ofReal.comp
    (continuous_const.mul (Real.continuous_rpow_const hb.le))
  simpa [Real.zero_rpow hb.ne'] using
    (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))

/-- Triangle inequality in the literal mixed norm, on compact smooth forces. -/
theorem grid_mixed_add {F G : SpaceTimeField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    mixedLebesgueENorm 1 2 (F + G) ≤
      mixedLebesgueENorm 1 2 F + mixedLebesgueENorm 1 2 G := by
  let U := fun t => (I02.slice_memLp hF.continuous hcF 2 t).toLp (fun x => F (t,x))
  let V := fun t => (I02.slice_memLp hG.continuous hcG 2 t).toLp (fun x => G (t,x))
  have hu : AEStronglyMeasurable U forceTimeMeasure :=
    (I02.continuous_slicePath hF.continuous hcF).stronglyMeasurable.aestronglyMeasurable
  have hv : AEStronglyMeasurable V forceTimeMeasure :=
    (I02.continuous_slicePath hG.continuous hcG).stronglyMeasurable.aestronglyMeasurable
  have hs : IsLebesgueSlicePath 2 (F + G) (U + V) := by
    intro t _
    filter_upwards [Lp.coeFn_add (U t) (V t),
      (I02.slice_memLp hF.continuous hcF 2 t).coeFn_toLp,
      (I02.slice_memLp hG.continuous hcG 2 t).coeFn_toLp] with x hx hfx hgx
    exact hx.trans (congrArg₂ (· + ·) hfx hgx)
  refine (iInf_le_of_le ⟨U + V, hs, hu.add hv⟩ le_rfl).trans ?_
  rw [mixedLebesgueENorm_eq hF.continuous hcF, mixedLebesgueENorm_eq hG.continuous hcG,
    ← I03.eLpNorm_slicePath_eq 2 hF.continuous hcF 1,
    ← I03.eLpNorm_slicePath_eq 2 hG.continuous hcG 1]
  exact eLpNorm_add_le hu hv le_rfl

/-- Compact homogeneous paths are additive, proved using the existing
integrability-carrying subtraction theorem and uniqueness. -/
theorem grid_homogeneous_add (hreal : I03.CompactHomogeneousRealization)
    {F G : SpaceTimeField} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    forceHomogeneousENorm 2 (-1) (F + G) ≤
      forceHomogeneousENorm 2 (-1) F + forceHomogeneousENorm 2 (-1) G := by
  let hs : (-3 / 2 : ℝ) < -1 := by norm_num
  let U := D01.Homogeneous.compactHomogeneousPath hs hF hcF
  let V := D01.Homogeneous.compactHomogeneousPath hs hG hcG
  let W := D01.Homogeneous.compactHomogeneousPath hs (hF.add hG) (hcF.add hcG)
  have he : W = U + V := by
    funext t
    have hf := I03.compactHomogeneousPath_slice hs hF hcF t
    have hg := I03.compactHomogeneousPath_slice hs hG hcG t
    have hw := I03.compactHomogeneousPath_slice hs (hF.add hG) (hcF.add hcG) t
    have hi {H : SpaceTimeField} (hh : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
        ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable (fun x => ψ x * ((H (t,x) i : ℝ) : ℂ)) :=
      D01.Homogeneous.integrable_schwartz_mul_component
        (D01.Homogeneous.compactSchwartzComponents
          (hh.comp (contDiff_const.prodMk contDiff_id))
          (I02.slice_hasCompactSupport hc t)) (fun _ _ => rfl)
    have hd := D01.Homogeneous.isHomogeneousSliceDatum_sub hw hg
      (hi (hF.add hG) (hcF.add hcG)) (hi hG hcG)
    have hfield : (fun x => F (t,x) + G (t,x)) - (fun x => G (t,x)) = fun x => F (t,x) := by
      ext x; simp
    rw [hfield] at hd
    have heq := D01.Homogeneous.isHomogeneousSliceDatum_unique hd hf
    exact sub_eq_iff_eq_add.mp heq
  change forceHomogeneousENorm 2 (-1) (fun x => F x + G x) ≤ _
  rw [I03.forceHomogeneousENorm_eq_path hreal hs (by norm_num) (hF.add hG) (hcF.add hcG),
    I03.forceHomogeneousENorm_eq_path hreal hs (by norm_num) hF hcF,
    I03.forceHomogeneousENorm_eq_path hreal hs (by norm_num) hG hcG]
  change eLpNorm W 2 forceTimeMeasure ≤ eLpNorm U 2 forceTimeMeasure + eLpNorm V 2 forceTimeMeasure
  rw [he]
  exact eLpNorm_add_le (hreal _ hs (by norm_num) F hF hcF)
    (hreal _ hs (by norm_num) G hG hcG) (by norm_num)

/-- The literal mixed-norm limit of the correction plus packet. -/
theorem grid_mixed_limit {ν : ℝ} {P : PacketAPI ν} (C : CorrectionAPI ν P) :
    Tendsto (fun ε : ℝ => mixedLebesgueENorm 1 2
      (C.forceCorrection ε + scaledForce P.force C.x₀ C.T ε)) (𝓝[>] 0) (𝓝 0) := by
  have hw : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) (scalingThreshold C) :=
    Ioc_mem_nhdsGT (scalingThreshold_pos C)
  have hc : Tendsto (fun ε : ℝ => mixedLebesgueENorm 1 2 (C.forceCorrection ε))
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (grid_power_limit (C.mixedConst 2 1) (3 / 2) (by norm_num))
      (Eventually.of_forall fun _ => zero_le)
    filter_upwards [hw] with ε hε
    have hb := C.force_mixed_bound 2 1 ε (mem_correction_range C hε)
    norm_num [alpha] at hb
    exact hb
  have hp : Tendsto (fun ε : ℝ => mixedLebesgueENorm 1 2
      (scaledForce P.force C.x₀ C.T ε)) (𝓝[>] 0) (𝓝 0) := by
    have hb := NSFormalization.Source.compact_force_mixed_tendsto_zero
      P.force_smooth P.force_support.1 2 1 (by norm_num)
      (fun ε => C.T - ε ^ 2) (fun _ => C.x₀)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
      (Eventually.of_forall fun _ => zero_le)
    exact Eventually.of_forall fun ε => by
      change mixedLebesgueENorm 1 2 (NSFormalization.Source.parabolicForce ε⁻¹
        (C.T - ε ^ 2) C.x₀ P.force) ≤ _
      rw [mixedLebesgueENorm_eq
        (NSFormalization.Source.parabolicForce_smooth _ _ _ P.force_smooth).continuous
        (NSFormalization.Source.parabolicForce_compact _ _ _ P.force_support.1)]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hsum := hc.add hp
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [hw] with ε hε
  exact grid_mixed_add (C.force_smooth ε (mem_correction_range C hε))
    (NSFormalization.Source.parabolicForce_smooth _ _ _ P.force_smooth)
    (C.force_compactSupport ε (mem_correction_range C hε))
    (NSFormalization.Source.parabolicForce_compact _ _ _ P.force_support.1)

/-- The sole conditional limit: homogeneous negative order. -/
theorem grid_homogeneous_limit (hreal : I03.CompactHomogeneousRealization)
    {ν : ℝ} {P : PacketAPI ν} (C : CorrectionAPI ν P) :
    Tendsto (fun ε : ℝ => forceHomogeneousENorm 2 (-1)
      (C.forceCorrection ε + scaledForce P.force C.x₀ C.T ε)) (𝓝[>] 0) (𝓝 0) := by
  have hw : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) (scalingThreshold C) :=
    Ioc_mem_nhdsGT (scalingThreshold_pos C)
  obtain ⟨K, hK⟩ := I03.correctionNegativeHomogeneous hreal C thresholds 2
    (by norm_num) (-1) (by norm_num) (by norm_num)
  have hc : Tendsto (fun ε : ℝ => forceHomogeneousENorm 2 (-1) (C.forceCorrection ε))
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (grid_power_limit K (3 / 2) (by norm_num))
      (Eventually.of_forall fun _ => zero_le)
    filter_upwards [hw] with ε hε
    have hb := hK ε hε
    norm_num [thresholds.formula] at hb
    exact hb
  have hp : Tendsto (fun ε : ℝ => forceHomogeneousENorm 2 (-1)
      (scaledForce P.force C.x₀ C.T ε)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (grid_power_limit (I03.packetHomogeneousConst P.force 2 (-1)) (1 / 2) (by norm_num))
      (Eventually.of_forall fun _ => zero_le)
    filter_upwards [hw] with ε hε
    have hb := I03.packetNegativeHomogeneous hreal P C.x₀ C.T
      (scalingThreshold C) thresholds 2 (by norm_num) (-1) (by norm_num) (by norm_num) ε hε
    norm_num [thresholds.formula] at hb
    exact hb
  have hsum := hc.add hp
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [hw] with ε hε
  exact grid_homogeneous_add hreal (C.force_smooth ε (mem_correction_range C hε))
    (NSFormalization.Source.parabolicForce_smooth _ _ _ P.force_smooth)
    (C.force_compactSupport ε (mem_correction_range C hε))
    (NSFormalization.Source.parabolicForce_compact _ _ _ P.force_support.1)

end BlowupDensity.Bindings
