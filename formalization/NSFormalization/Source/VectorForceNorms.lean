import NSFormalization.Source.FourierTranslation
import NSFormalization.Paper3.CompactFourierTime
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Vector-valued force norms and arbitrary insertion centers

The vector Sobolev norm is the Euclidean combination of the three scalar
Fourier energies. Thus this module applies the scalar Fourier analysis to the
actual real three-component forces in the Navier--Stokes equation.
-/

noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory Filter Topology
open scoped ContDiff ENNReal

def coordinateForce (F : VelocityField) (i : Fin 3) : SpaceTime → ℂ :=
  fun z => (F z i : ℂ)

def vectorFourierSobolevNorm (s : ℝ) (F : VelocityField) (t : ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin 3, fourierSobolevSq s (fun x => coordinateForce F i (t, x)))

theorem coordinateForce_smooth {F : VelocityField} (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    ContDiff ℝ ∞ (coordinateForce F i) :=
  Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hF)

theorem coordinateForce_compact {F : VelocityField} (hF : HasCompactSupport F) (i : Fin 3) :
    HasCompactSupport (coordinateForce F i) := by
  exact hF.comp_left (g := fun v : Space => (v i : ℂ)) (by simp)

theorem fourierSobolevSq_nonneg (s : ℝ) (f : Space → ℂ) : 0 ≤ fourierSobolevSq s f :=
  integral_nonneg (fun _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))

theorem vectorFourierSobolevNorm_le_sum (s : ℝ) (F : VelocityField) (t : ℝ) :
    vectorFourierSobolevNorm s F t ≤
      ∑ i : Fin 3, fourierSobolevNorm s (fun x => coordinateForce F i (t, x)) := by
  unfold vectorFourierSobolevNorm
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  · have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i : Fin 3 => fourierSobolevNorm s (fun x => coordinateForce F i (t, x)))
      (fun _ _ => Real.sqrt_nonneg _)
    simpa only [fourierSobolevNorm, Real.sq_sqrt (fourierSobolevSq_nonneg _ _)] using h

theorem eLpNorm_vector_le_sum (s : ℝ) (F : VelocityField) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (hF : ∀ i : Fin 3, AEStronglyMeasurable
      (fun t => fourierSobolevNorm s (fun x => coordinateForce F i (t, x))) volume) :
    eLpNorm (vectorFourierSobolevNorm s F) q volume ≤
      ∑ i : Fin 3, eLpNorm
        (fun t => fourierSobolevNorm s (fun x => coordinateForce F i (t, x))) q volume := by
  have hb (t : ℝ) : ‖vectorFourierSobolevNorm s F t‖ ≤
      ∑ i : Fin 3, fourierSobolevNorm s (fun x => coordinateForce F i (t, x)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ vectorFourierSobolevNorm s F t from Real.sqrt_nonneg _)]
    exact vectorFourierSobolevNorm_le_sum s F t
  have hm := eLpNorm_mono_real (p := q) (μ := volume) hb
  refine hm.trans ?_
  have he : (∑ i : Fin 3, fun t => fourierSobolevNorm s
      (fun x => coordinateForce F i (t, x))) =
      (fun t => ∑ i : Fin 3, fourierSobolevNorm s (fun x => coordinateForce F i (t, x))) := by
    funext t
    simp only [Finset.sum_apply]
  have hs := eLpNorm_sum_le (f := fun i : Fin 3 =>
      fun t => fourierSobolevNorm s (fun x => coordinateForce F i (t, x)))
      (s := Finset.univ) (fun i _ => hF i) hq
  rw [he] at hs
  exact hs

theorem coordinate_parabolicForce (k t₀ : ℝ) (x₀ : Space) (F : VelocityField)
    (i : Fin 3) (t : ℝ) :
    (fun x => coordinateForce (parabolicForce k t₀ x₀ F) i (t, x)) =
      fun x => parabolicComplexForce k t₀ (fun t x => coordinateForce F i (t, x)) t (x - x₀) := by
  funext x
  simp [coordinateForce, parabolicForce, dilateField, parabolicComplexForce,
    concentratedForce, PiLp.smul_apply, Complex.ofReal_mul, smul_eq_mul]

theorem coordinate_norm_parabolicForce (s k t₀ : ℝ) (x₀ : Space) (F : VelocityField)
    (i : Fin 3) (t : ℝ) :
    fourierSobolevNorm s (fun x => coordinateForce (parabolicForce k t₀ x₀ F) i (t, x)) =
      fourierSobolevNorm s (parabolicComplexForce k t₀
        (fun t x => coordinateForce F i (t, x)) t) := by
  rw [coordinate_parabolicForce, fourierSobolevNorm_translate]

theorem parabolicForce_smooth (k t₀ : ℝ) (x₀ : Space) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (parabolicForce k t₀ x₀ F) := by
  exact (contDiff_const (c := k ^ 3)).smul (hF.comp (by
    change ContDiff ℝ ∞ (fun z : SpaceTime => (k ^ 2 * (z.1 - t₀), k • (z.2 - x₀)))
    fun_prop))

/-- Component convergence aggregates for any actual smooth family, including
the background correction forces whose profile depends on epsilon. -/
theorem vector_family_tendsto_zero_of_components (s : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q)
    {F : ℝ → VelocityField} (hF : ∀ ε, ContDiff ℝ ∞ (F ε))
    (hcomponents : ∀ i : Fin 3, Tendsto (fun ε : ℝ => eLpNorm
      (fun t => fourierSobolevNorm s (fun x => coordinateForce (F ε) i (t, x))) q volume)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s (F ε)) q volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hsum := tendsto_finsetSum (s := Finset.univ) (fun i _ => hcomponents i)
  simp only [Finset.sum_const_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall (fun _ => bot_le)
  · exact Eventually.of_forall (fun ε => eLpNorm_vector_le_sum s (F ε) q hq
      (fun i => (Paper3.stronglyMeasurable_fourierSobolev_time s
        (coordinateForce_smooth (hF ε) i).continuous).aestronglyMeasurable))

/-- Convergence of the three scalar Fourier time norms implies convergence
of the actual vector norm, for any time and spatial center depending on epsilon. -/
theorem vector_force_tendsto_zero_of_components (s : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (center : ℝ → ℝ) (spatialCenter : ℝ → Space) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F)
    (hcomponents : ∀ i : Fin 3, Tendsto (fun ε : ℝ => eLpNorm (fun t =>
      fourierSobolevNorm s (parabolicComplexForce ε⁻¹ (center ε)
        (fun t x => coordinateForce F i (t, x)) t)) q volume) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s
      (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F)) q volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hsum := tendsto_finsetSum (s := Finset.univ) (fun i _ => hcomponents i)
  simp only [Finset.sum_const_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall (fun _ => bot_le)
  · apply Eventually.of_forall
    intro ε
    have hm := eLpNorm_vector_le_sum s
      (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F) q hq (fun i =>
        (Paper3.stronglyMeasurable_fourierSobolev_time s
          (coordinateForce_smooth (parabolicForce_smooth _ _ _ hF) i).continuous).aestronglyMeasurable)
    simpa only [coordinate_norm_parabolicForce] using hm

end NSFormalization.Source
