import NavierStokes.R3SpaceTime
import NavierStokes.R3RieszApproximation

/-!
# Spatial convolution of integrable space-time functions

The spatial kernel is a measure on the zero-time slice. Fubini and translation
invariance give its space-time Fourier multiplier without differentiating
in time or requiring pointwise temperedness of the physical pressure.
-/

noncomputable section
namespace NavierStokes.R3SpatialConvolution

open Set Filter MeasureTheory FourierTransform R3SpaceTime ProblemStatement
open scoped SchwartzMap Topology FourierTransform

def spaceInj (x : Space) : Domain := pack 0 x

theorem spaceInj_isometry : Isometry spaceInj :=
  isometry_iff_dist_eq.mpr fun x y => WithLp.dist_toLp_snd 2 ℝ Space x y

theorem spaceInj_measurableEmbedding : MeasurableEmbedding spaceInj :=
  spaceInj_isometry.isClosedEmbedding.measurableEmbedding

def spatialMeasure : Measure Domain := volume.map spaceInj

instance : SFinite spatialMeasure := inferInstanceAs (SFinite (volume.map spaceInj))

theorem integral_spatialMeasure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain → F) : ∫ z, f z ∂spatialMeasure = ∫ x : Space, f (spaceInj x) :=
  spaceInj_measurableEmbedding.integral_map f

theorem integrable_spatialMeasure_iff {F : Type*} [NormedAddCommGroup F]
    (f : Domain → F) : Integrable f spatialMeasure ↔ Integrable (fun x : Space => f (spaceInj x)) :=
  spaceInj_measurableEmbedding.integrable_map_iff

theorem inner_spaceInj (x : Space) (z : Domain) :
    inner ℝ (spaceInj x) z = inner ℝ x (spaceProj z) := by
  simp [spaceInj, pack, WithLp.prod_inner_apply, spaceProj, WithLp.sndL]

/-- A convolution with an arbitrary sigma-finite kernel measure and an
integrable Lebesgue function has the expected Fourier transform. -/
theorem fourier_convolution_measure {μ : Measure Domain} [SFinite μ]
    {K g : Domain → ℂ} (hK : Integrable K μ) (hg : Integrable g) (ξ : Domain) :
    𝓕 (fun z : Domain => ∫ y, K y * g (z - y) ∂μ) ξ =
      (∫ y, Real.fourierChar (-inner ℝ y ξ) • K y ∂μ) * 𝓕 g ξ := by
  have hi := hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hchar : Integrable (fun zy : Domain × Domain =>
      Real.fourierChar (-inner ℝ zy.1 ξ) • (K zy.2 * g (zy.1 - zy.2))) (volume.prod μ) := by
    apply hi.mono
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable
    · filter_upwards with zy
      simp
  calc
    _ = ∫ z : Domain, ∫ y, Real.fourierChar (-inner ℝ z ξ) • (K y * g (z - y)) ∂μ := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards with z
      simp only [Circle.smul_def, integral_const_mul, smul_eq_mul]
    _ = ∫ y, (∫ z : Domain, Real.fourierChar (-inner ℝ z ξ) • (K y * g (z - y))) ∂μ :=
      integral_integral_swap hchar
    _ = ∫ y, (∫ z : Domain, Real.fourierChar (-inner ℝ (z + y) ξ) • (K y * g z)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      have he := integral_add_right_eq_self
        (fun z : Domain => Real.fourierChar (-inner ℝ z ξ) • (K y * g (z - y))) y
        (μ := volume)
      simpa only [add_sub_cancel_right] using he.symm
    _ = ∫ y, (Real.fourierChar (-inner ℝ y ξ) • K y) * 𝓕 g ξ ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [Real.fourier_eq, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      simp only [inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.smul_def,
        Circle.coe_mul, smul_eq_mul]
      ring
    _ = _ := integral_mul_const _ _

def regularized (n : ℕ) (i j : Fin 3) (g : Domain → ℂ) (z : Domain) : ℂ :=
  ∫ y : Space, R3RieszKernel.truncatedKernel n i j y * g (pack (timeProj z) (spaceProj z - y))

theorem regularized_eq_convolution (n : ℕ) (i j : Fin 3) (g : Domain → ℂ) (z : Domain) :
    regularized n i j g z = ∫ y, R3RieszKernel.truncatedKernel n i j (spaceProj y) *
      g (z - y) ∂spatialMeasure := by
  rw [integral_spatialMeasure]
  unfold regularized
  apply integral_congr_ae
  filter_upwards with y
  congr 2
  change WithLp.toLp 2 (timeProj z, spaceProj z - y) =
    WithLp.toLp 2 (timeProj z - 0, spaceProj z - y)
  simp only [sub_zero]

theorem liftedKernel_integrable (n : ℕ) (i j : Fin 3) :
    Integrable (fun z : Domain => R3RieszKernel.truncatedKernel n i j (spaceProj z)) spatialMeasure :=
  (integrable_spatialMeasure_iff _).mpr (R3RieszKernel.truncatedKernel_integrable n i j)

theorem regularized_integrable (n : ℕ) (i j : Fin 3) {g : Domain → ℂ} (hg : Integrable g) :
    Integrable (regularized n i j g) := by
  simp only [funext (regularized_eq_convolution n i j g)]
  exact ((liftedKernel_integrable n i j).convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) hg).integral_prod_left

theorem regularized_fourier (n : ℕ) (i j : Fin 3) {g : Domain → ℂ}
    (hg : Integrable g) (ξ : Domain) :
    𝓕 (regularized n i j g) ξ =
      𝓕 (R3RieszKernel.truncatedKernel n i j) (spaceProj ξ) * 𝓕 g ξ := by
  rw [funext (regularized_eq_convolution n i j g),
    fourier_convolution_measure (liftedKernel_integrable n i j) hg, integral_spatialMeasure]
  congr 1
  simp only [inner_spaceInj]
  rfl

end NavierStokes.R3SpatialConvolution
