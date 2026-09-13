import NSFormalization.Source.VectorForceNorms
import NSFormalization.Paper3.HomogeneousTime
import NSFormalization.Paper3.PositiveFourierTime
import NSFormalization.Paper3.Thresholds

/-!
# Concrete compact-force convergence below the whole-space thresholds

The input is an actual smooth compact spacetime force. Slice integrability,
time measurability and finite time norms are derived, rather than left as
assumptions of the convergence theorem. All negative Sobolev orders are
handled by monotonicity through a valid intermediate homogeneous order.
-/
noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory Filter Topology
open scoped ContDiff ENNReal FourierTransform

theorem concentratedForce_smooth (k : ℝ) {f : Space → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (concentratedForce k f) := by
  convert (contDiff_const (c := k ^ 3)).smul
    (hf.comp ((contDiff_const (c := k)).smul contDiff_id)) using 1
  funext x
  rfl

theorem concentratedForce_compact {k : ℝ} (hk : k ≠ 0) {f : Space → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (concentratedForce k f) := by
  apply HasCompactSupport.intro ((hf : IsCompact (tsupport f)).image
    (show Continuous (fun x : Space => k⁻¹ • x) by fun_prop))
  intro x hx
  have hn : k • x ∉ tsupport f := by
    intro hn
    exact hx ⟨k • x, hn, by simp [smul_smul, hk]⟩
  simp [concentratedForce, image_eq_zero_of_notMem_tsupport hn]

theorem fourierSobolevNorm_mono_of_compact {s r : ℝ} (hsr : s ≤ r)
    {f : Space → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    fourierSobolevNorm s f ≤ fourierSobolevNorm r f := by
  apply Real.sqrt_le_sqrt
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc
  exact Paper3.integral_besselIntegrand_mono hsr (𝓕 φ).continuous
    (Paper3.compact_fourier_bessel_integrable r f hf hc)

theorem scalar_force_eLpNorm_mono {s r k : ℝ} (hsr : s ≤ r) (hk : k ≠ 0)
    (t₀ : ℝ) (q : ℝ≥0∞) {F : SpaceTime → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    eLpNorm (fun t => fourierSobolevNorm s
      (parabolicComplexForce k t₀ (fun t x => F (t, x)) t)) q volume ≤
    eLpNorm (fun t => fourierSobolevNorm r
      (parabolicComplexForce k t₀ (fun t x => F (t, x)) t)) q volume := by
  apply eLpNorm_mono_real
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (show 0 ≤ fourierSobolevNorm s _ from Real.sqrt_nonneg _)]
  exact fourierSobolevNorm_mono_of_compact hsr
    (concentratedForce_smooth k (hF.comp (contDiff_const.prodMk contDiff_id)))
    (concentratedForce_compact hk (Paper3.compact_spatial_slice hc _))

theorem compact_scalar_force_L1_zero_tendsto {F : SpaceTime → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (center : ℝ → ℝ) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => fourierSobolevNorm 0
      (parabolicComplexForce ε⁻¹ (center ε) (fun t x => F (t, x)) t)) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply force_positive_tendsto_zero (s := 0) le_rfl 1 (by norm_num) center
  · exact Paper3.compact_spacetime_fourier_slice_continuous hF hc
  · exact Paper3.compact_spacetime_bessel_slices 0 hF hc
  · exact Paper3.stronglyMeasurable_fourierSobolev_time 0 hF.continuous
  · exact (Paper3.memLp_fourierSobolev_nonpositive_time le_rfl hF hc 1).eLpNorm_ne_top

theorem compact_scalar_force_L1_nonpositive_tendsto {s : ℝ} (hs : s ≤ 0)
    {F : SpaceTime → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => fourierSobolevNorm s
      (parabolicComplexForce ε⁻¹ (center ε) (fun t x => F (t, x)) t)) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (compact_scalar_force_L1_zero_tendsto hF hc center)
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact scalar_force_eLpNorm_mono hs (inv_ne_zero (ne_of_gt hε)) (center ε) 1 hF hc

theorem compact_scalar_force_L1_tendsto {s : ℝ} (hs : s < 1 / 2)
    {F : SpaceTime → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => fourierSobolevNorm s
      (parabolicComplexForce ε⁻¹ (center ε) (fun t x => F (t, x)) t)) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  by_cases hs0 : s ≤ 0
  · exact compact_scalar_force_L1_nonpositive_tendsto hs0 hF hc center
  · apply force_positive_tendsto_zero (le_of_not_ge hs0) 1 (by norm_num; linarith) center
    · exact Paper3.compact_spacetime_fourier_slice_continuous hF hc
    · exact Paper3.compact_spacetime_bessel_slices s hF hc
    · exact Paper3.stronglyMeasurable_fourierSobolev_time s hF.continuous
    · exact (Paper3.memLp_fourierSobolev_le_one_time (by linarith) hF hc 1).eLpNorm_ne_top

/-- Every compact smooth scalar force converges in `L² H^s` for all `s<-1/2`,
including `s≤-3/2`, where a direct homogeneous scaling claim would be false. -/
theorem compact_scalar_force_L2_tendsto {s : ℝ} (hs : s < -1 / 2)
    {F : SpaceTime → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) :
    Tendsto (fun ε : ℝ => eLpNorm (fun t => fourierSobolevNorm s
      (parabolicComplexForce ε⁻¹ (center ε) (fun t x => F (t, x)) t)) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨r, hrlo, hrhi, hsr⟩ := Paper3.negative_intermediate_index hs
  have hr0 : r ≤ 0 := by linarith
  have ht : Tendsto (fun ε : ℝ => eLpNorm (fun t => fourierSobolevNorm r
      (parabolicComplexForce ε⁻¹ (center ε) (fun t x => F (t, x)) t)) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
    apply force_negative_tendsto_zero hr0 2 (by norm_num; linarith) center
    · exact Paper3.compact_spacetime_fourier_slice_continuous hF hc
    · intro t
      exact Paper3.compact_fourier_homogeneous_negative_integrable hrlo hr0 _
        (hF.comp (contDiff_const.prodMk contDiff_id)) (Paper3.compact_spatial_slice hc t)
    · exact Paper3.stronglyMeasurable_homogeneousFourier_time r hF.continuous
    · exact (Paper3.memLp_homogeneousFourier_time hrlo hr0 hF hc 2).eLpNorm_ne_top
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact scalar_force_eLpNorm_mono hsr.le (inv_ne_zero (ne_of_gt hε)) (center ε) 2 hF hc

/-- The preceding estimate applies to the actual three-component physical
force, with arbitrary moving spatial and time insertion centers. -/
theorem compact_vector_force_L2_tendsto {s : ℝ} (hs : s < -1 / 2)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) (spatialCenter : ℝ → Space) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s
      (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply vector_force_tendsto_zero_of_components s 2 (by norm_num) center spatialCenter hF
  intro i
  exact compact_scalar_force_L2_tendsto hs (coordinateForce_smooth hF i)
    (coordinateForce_compact hc i) center

theorem compact_vector_force_L1_nonpositive_tendsto {s : ℝ} (hs : s ≤ 0)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) (spatialCenter : ℝ → Space) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s
      (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply vector_force_tendsto_zero_of_components s 1 le_rfl center spatialCenter hF
  intro i
  exact compact_scalar_force_L1_nonpositive_tendsto hs (coordinateForce_smooth hF i)
    (coordinateForce_compact hc i) center

/-- The full first subcritical range for actual vector forces. -/
theorem compact_vector_force_L1_tendsto {s : ℝ} (hs : s < 1 / 2)
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) (spatialCenter : ℝ → Space) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s
      (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) 1 volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply vector_force_tendsto_zero_of_components s 1 le_rfl center spatialCenter hF
  intro i
  exact compact_scalar_force_L1_tendsto hs (coordinateForce_smooth hF i)
    (coordinateForce_compact hc i) center

end NSFormalization.Source
