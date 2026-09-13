import NSFormalization.Paper1.PeriodicSmoothSobolev
import NSFormalization.Paper1.PeriodicForceTopology

/-!
# Genuine norm bounds for smooth periodic test forces

The Fourier gauge of a smooth periodic field is realized in weighted `ℓ²`.
Its three component norms are combined in Euclidean norm, giving the vector
triangle inequality without an assumed pointwise comparison.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicTestForceNorm

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicForceTopology
open scoped ContDiff ENNReal Topology

private theorem sobolevSq_nonneg (s : ℝ) (f : Space → ℂ) :
    0 ≤ periodicSobolevSq s f :=
  tsum_nonneg (fun k => mul_nonneg
    (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) s)
    (sq_nonneg _))

private theorem vectorNorm_eq_componentNorms (s : ℝ) (F : VelocityField) (t : ℝ) :
    periodicVectorSobolevNorm s F t = ‖WithLp.toLp 2 (fun i : Fin 3 =>
      periodicSobolevNorm s (fun x => coordinateForce F i (t, x)))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs, periodicSobolevNorm,
    Real.sq_sqrt (sobolevSq_nonneg _ _)]
  rfl

/-- The genuine vector Fourier norm satisfies the triangle inequality for
smooth periodic spacetime fields at every real Sobolev order. -/
theorem periodicVectorSobolevNorm_add_le
    {F G : VelocityField} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFp : UnitSpatialPeriodsOn univ F) (hGp : UnitSpatialPeriodsOn univ G)
    (s t : ℝ) : periodicVectorSobolevNorm s (F + G) t ≤
      periodicVectorSobolevNorm s F t + periodicVectorSobolevNorm s G t := by
  let A : Space := WithLp.toLp 2 (fun i : Fin 3 =>
    periodicSobolevNorm s (fun x => coordinateForce F i (t, x)))
  let B : Space := WithLp.toLp 2 (fun i : Fin 3 =>
    periodicSobolevNorm s (fun x => coordinateForce G i (t, x)))
  let C : Space := WithLp.toLp 2 (fun i : Fin 3 =>
    periodicSobolevNorm s (fun x => coordinateForce (F + G) i (t, x)))
  have hi (i : Fin 3) : C i ≤ A i + B i := by
    have hsF : ContDiff ℝ ∞ (fun x : Space => coordinateForce F i (t, x)) :=
      (coordinateForce_smooth hF i).comp (contDiff_const.prodMk contDiff_id)
    have hsG : ContDiff ℝ ∞ (fun x : Space => coordinateForce G i (t, x)) :=
      (coordinateForce_smooth hG i).comp (contDiff_const.prodMk contDiff_id)
    have hpF : UnitPeriods (fun x => coordinateForce F i (t, x)) := by
      intro x j
      exact congrArg (fun v : Space => (v i : ℂ)) (hFp t (mem_univ _) x j)
    have hpG : UnitPeriods (fun x => coordinateForce G i (t, x)) := by
      intro x j
      exact congrArg (fun v : Space => (v i : ℂ)) (hGp t (mem_univ _) x j)
    have hadd : (fun x => coordinateForce (F + G) i (t, x)) =
        (fun x => coordinateForce F i (t, x)) +
          (fun x => coordinateForce G i (t, x)) := by
      funext x
      simp [coordinateForce]
    dsimp [A, B, C]
    rw [hadd]
    exact periodicSobolevNorm_add_le_smooth hsF hsG hpF hpG s
  have hnorm : ‖C‖ ≤ ‖A + B‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    simp only [Real.norm_eq_abs, sq_abs, PiLp.add_apply]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hi i) 2
  rw [vectorNorm_eq_componentNorms, vectorNorm_eq_componentNorms,
    vectorNorm_eq_componentNorms]
  exact hnorm.trans (norm_add_le A B)

/-- Negation and subtraction preserve the actual smooth test-force class. -/
theorem isTestForce_neg {F : VelocityField} (hF : IsTestForce F) : IsTestForce (-F) := by
  refine ⟨hF.smooth.neg, ?_, ?_⟩
  · intro t ht x i
    exact congrArg Neg.neg (hF.periodic t ht x i)
  · simpa only [tsupport_neg] using hF.time_support

theorem isTestForce_sub {F G : VelocityField} (hF : IsTestForce F)
    (hG : IsTestForce G) : IsTestForce (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add (isTestForce_neg hG)

/-- All pointwise comparison hypotheses in the earlier force-distance
triangle interface are now consequences of smooth test-force membership. -/
theorem forceDistance_triangle_of_testForces
    {F G H : VelocityField} (hF : IsTestForce F) (hG : IsTestForce G)
    (hH : IsTestForce H) (s : ℝ) :
    forceDistance s F H ≤ forceDistance s F G + forceDistance s G H := by
  apply forceDistance_triangle
    (stronglyMeasurable_forceProfile_of_testForces hF hG s).aestronglyMeasurable
    (stronglyMeasurable_forceProfile_of_testForces hG hH s).aestronglyMeasurable
  intro t
  have hFG := isTestForce_sub hF hG
  have hGH := isTestForce_sub hG hH
  have he : F - H = (F - G) + (G - H) := by abel
  change periodicVectorSobolevNorm s (F - H) t ≤ _
  rw [he]
  exact periodicVectorSobolevNorm_add_le hFG.smooth hGH.smooth
    hFG.periodic hGH.periodic s t

end NSFormalization.Paper1.PeriodicTestForceNorm
