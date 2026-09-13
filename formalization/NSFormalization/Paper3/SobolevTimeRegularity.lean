import NSFormalization.Paper3.SpatiallyCompactTime

/-! Genuine Banach-valued time regularity in the weighted Fourier L²
representation of Sobolev space. -/
noncomputable section
namespace NSFormalization.Paper3
open Set Filter MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff ENNReal Topology

/-- A smooth uniformly spatially compact family defines actual Sobolev vectors
by wrapping each original slice and applying the weighted Fourier L² map. -/
def sobolevTimeSlice (s : ℝ) (F : ℝ × Space → ℂ) (hF : ContDiff ℝ ∞ F)
    {K : Set Space} (hK : IsCompact K) (hz : ∀ t x, x ∉ K → F (t, x) = 0) (t : ℝ) :
    Lp ℂ 2 (volume : Measure Space) :=
  compactFourierLp s (fun x => F (t, x))
    (hF.comp (contDiff_const.prodMk contDiff_id)) (family_slice_compact hK hz t)

 theorem norm_sobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F)
    {K : Set Space} (hK : IsCompact K) (hz : ∀ t x, x ∉ K → F (t, x) = 0) (t : ℝ) :
    ‖sobolevTimeSlice s F hF hK hz t‖ = NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x)) :=
  norm_compactFourierLp s _ _ _

/-- The Banach norm of a difference is the actual Sobolev norm of the original
physical difference, because the entire weighted Fourier L² map is linear. -/
theorem norm_sobolevTimeSlice_sub (s : ℝ) {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F)
    {K : Set Space} (hK : IsCompact K) (hz : ∀ t x, x ∉ K → F (t, x) = 0) (t a : ℝ) :
    ‖sobolevTimeSlice s F hF hK hz t - sobolevTimeSlice s F hF hK hz a‖ =
      NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x) - F (a, x)) := by
  unfold sobolevTimeSlice compactFourierLp
  rw [← map_sub, norm_weightedFourierLp]
  rfl

 theorem tendsto_sobolevNorm_difference (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) (a : ℝ) :
    Tendsto (fun t => NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x) - F (a, x)))
      (𝓝 a) (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_nat_ge s
  have he : Tendsto (fun t => ∫ ξ : Space,
      besselIntegrand s (𝓕 (fun x => F (t, x) - F (a, x))) ξ) (𝓝 a) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_bessel_nat_difference n hF hK hz a)
      (fun t => integral_nonneg (fun ξ => by unfold besselIntegrand; positivity))
    intro t
    let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x) - F (a, x))
      ((hF.comp (contDiff_const.prodMk contDiff_id)).sub (hF.comp (contDiff_const.prodMk contDiff_id)))
      ((family_slice_compact hK hz t).sub (family_slice_compact hK hz a))
    exact integral_besselIntegrand_mono hn (𝓕 φ).continuous (schwartz_bessel_integrable (n : ℝ) (𝓕 φ))
  simpa only [Function.comp_def, Real.sqrt_zero, NSFormalization.Source.fourierSobolevNorm,
    NSFormalization.Source.fourierSobolevSq, besselIntegrand] using Real.continuous_sqrt.continuousAt.tendsto.comp he

/-- Genuine continuity of the actual `Lp ℂ 2 volume` Sobolev vectors at every
real order. This is stronger than measurability or boundedness of a scalar norm. -/
theorem continuous_sobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F)
    {K : Set Space} (hK : IsCompact K) (hz : ∀ t x, x ∉ K → F (t, x) = 0) :
    Continuous (sobolevTimeSlice s F hF hK hz) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_sobolevTimeSlice_sub s hF hK hz] using tendsto_sobolevNorm_difference s hF hK hz a

end NSFormalization.Paper3
