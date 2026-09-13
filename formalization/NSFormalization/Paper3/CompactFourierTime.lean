import NSFormalization.Paper3.CompactFourier
import NSFormalization.Source.TimeNormScaling
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Compact spacetime forces and actual Fourier time profiles

The time profiles below are the actual square roots of Fourier energy integrals
used by `Source.TimeNormScaling`. Measurability is obtained by parameterized
Bochner integration, and time compactness from the joint support projection.
-/

noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff

/-- Every spatial slice of a spacetime compact function is compactly supported,
inside the fixed spatial projection of its support. -/
theorem compact_spatial_slice {F : ℝ × Space → ℂ} (hc : HasCompactSupport F) (t : ℝ) :
    HasCompactSupport (fun x : Space => F (t, x)) := by
  apply HasCompactSupport.intro ((hc : IsCompact (tsupport F)).image continuous_snd)
  intro x hx
  apply image_eq_zero_of_notMem_tsupport (f := F)
  intro htx
  exact hx ⟨(t, x), htx, rfl⟩

/-- All actual Fourier slice integrals required by the inhomogeneous force
scaling theorem are finite for a compact smooth spacetime input. -/
theorem compact_spacetime_bessel_slices (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 (fun x => F (t, x)) ξ‖ ^ 2) :=
  compact_fourier_bessel_integrable s _
    (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)

 theorem compact_spacetime_fourier_slice_continuous {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    Continuous (𝓕 (fun x => F (t, x))) := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x))
    (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)
  exact (𝓕 φ).continuous

/-- The actual spatial Fourier transform is jointly strongly measurable in
time and frequency, obtained by integrating a continuous phase integrand. -/
theorem stronglyMeasurable_spacetime_fourier {F : ℝ × Space → ℂ} (hF : Continuous F) :
    StronglyMeasurable (fun z : ℝ × Space => 𝓕 (fun x => F (z.1, x)) z.2) := by
  have hphase : Continuous (fun z : (ℝ × Space) × Space =>
      Complex.exp ((↑(-2 * Real.pi * inner ℝ z.2 z.1.2) : ℂ) * Complex.I) • F (z.1.1, z.2)) := by
    fun_prop
  have h := hphase.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure Space))
  simpa only [Real.fourier_eq'] using h

/-- No slice-integrability assumption is needed for measurability itself. -/
theorem stronglyMeasurable_fourierSobolev_time (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : Continuous F) :
    StronglyMeasurable (fun t => NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x))) := by
  have hFourier := stronglyMeasurable_spacetime_fourier hF
  have hi : StronglyMeasurable (fun z : ℝ × Space =>
      (1 + ‖z.2‖ ^ 2) ^ s * ‖𝓕 (fun x => F (z.1, x)) z.2‖ ^ 2) := by
    apply Measurable.stronglyMeasurable
    have hmeas := hFourier.measurable
    fun_prop
  exact Real.continuous_sqrt.comp_stronglyMeasurable hi.integral_prod_right'

 theorem stronglyMeasurable_homogeneousFourier_time (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : Continuous F) :
    StronglyMeasurable (fun t => NSFormalization.Source.homogeneousFourierNorm s (fun x => F (t, x))) := by
  have hFourier := stronglyMeasurable_spacetime_fourier hF
  have hi : StronglyMeasurable (fun z : ℝ × Space =>
      ‖z.2‖ ^ (2 * s) * ‖𝓕 (fun x => F (z.1, x)) z.2‖ ^ 2) := by
    apply Measurable.stronglyMeasurable
    have hmeas := hFourier.measurable
    fun_prop
  exact Real.continuous_sqrt.comp_stronglyMeasurable hi.integral_prod_right'

/-- The actual inhomogeneous norm profile vanishes outside the compact time
projection of the original spacetime support. -/
theorem compact_fourierSobolev_time (s : ℝ) {F : ℝ × Space → ℂ} (hc : HasCompactSupport F) :
    HasCompactSupport (fun t => NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x))) := by
  apply HasCompactSupport.intro ((hc : IsCompact (tsupport F)).image continuous_fst)
  intro t ht
  have hz : (fun x : Space => F (t, x)) = 0 := by
    funext x
    apply image_eq_zero_of_notMem_tsupport (f := F)
    intro htx
    exact ht ⟨(t, x), htx, rfl⟩
  simp [hz, NSFormalization.Source.fourierSobolevNorm, NSFormalization.Source.fourierSobolevSq,
    Real.fourier_eq]

 theorem compact_homogeneousFourier_time (s : ℝ) {F : ℝ × Space → ℂ} (hc : HasCompactSupport F) :
    HasCompactSupport (fun t => NSFormalization.Source.homogeneousFourierNorm s (fun x => F (t, x))) := by
  apply HasCompactSupport.intro ((hc : IsCompact (tsupport F)).image continuous_fst)
  intro t ht
  have hz : (fun x : Space => F (t, x)) = 0 := by
    funext x
    apply image_eq_zero_of_notMem_tsupport (f := F)
    intro htx
    exact ht ⟨(t, x), htx, rfl⟩
  simp [hz, NSFormalization.Source.homogeneousFourierNorm, Real.fourier_eq]

end NSFormalization.Paper3
